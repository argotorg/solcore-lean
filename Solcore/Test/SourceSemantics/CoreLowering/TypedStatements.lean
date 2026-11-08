import Solcore.SourceSemantics.CoreLowering.Internal.Statements.BuiltinCalls
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.Frontend.ProgramChecking
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRecursive
import Solcore.Frontend.SourceCore.CompatibleFunctions
import Solcore.Frontend.SourceCore.Internal.Carriers
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericLexical
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaValues
import Solcore.Test.SourceSemantics.CoreLowering.UnifiedCorpusSupport
import Solcore.Test.SourceSemantics.CoreLowering.Foundations.ReachableDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedImperative
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedImperativeForTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedLexicalControl
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedLexicalWhile
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedNamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedScopedControl
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedStatements

/-!
# Typed statement tests

Typed lexical, scoped and imperative statements, their headers and named parameters.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreTypedBuiltinCalls
/-! Actual builtin lowering closes concrete General argument meanings. Finite
reflection constructs the source call from native completion alone. Runtime
fixtures put general compound-key reads, short circuit and faults in arguments. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace Tests.SourceCoreTypedBuiltinCalls
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap ReadOnly

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"typed_builtin", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "typed_builtin.solc"⟩, 0, 1⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def literalNode : ExpressionNode := {
  id := id 0, span, type := .word, form := .literal (.decimal "7")}
private def calleeNode : ExpressionNode := {
  id := id 1, span, type := BuiltinFunctionId.wordToInteger.type,
  form := .reference "wordToInteger" (.builtinFunction .wordToInteger)}
private def callNode : ExpressionNode := {
  id := id 2, span, type := .integer,
  form := .call (id 1) [id 0] (.builtinFunction .wordToInteger)}
private def source : TypedSource := {
  owner, inputs := [], roots := [.expression (id 2)],
  nodes := [.expression literalNode, .expression calleeNode, .expression callNode]}
private theorem checkedExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [.word, .integer]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.word, .integer]).toOption.get checkedExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def literalCode : SourceCoreBasic.LoweredExpr := ⟨.word, LanguageResult.success (.word (Word.ofNatModulo 7))⟩
private def reasonAt : ExpressionId → Word := fun _ => Word.zero
private def policy (native : SourceCoreGeneralFunctions.CallableContext) : SourceCoreFunctions.Policy :=
  {SourceCoreCompatibleDataExpressions.functionPolicy 100 values with
    callables := SourceCoreGeneralFunctions.callablePolicy (some native) []}
private theorem literalTree (native : SourceCoreGeneralFunctions.CallableContext) {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody 2 compilation source [] (id 0) reasonAt = .ok code) :
    CompatibleExpressionGeneral.Tree 100 values source context [] reasonAt [] (id 0) code :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal
    (CompatibleExpressionLiterals.of_functions (values := values) (node := literalNode) (by rfl)
      (.word _) (by intro absent; cases absent) (by intros; rfl) rfl rfl accepted)))))))
private theorem certified (native : SourceCoreGeneralFunctions.CallableContext)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.builtin .wordToInteger))
    {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody 3 compilation source [] (id 2) reasonAt = .ok code) :
    BuiltinCalls.Typed.Tree 100 values source context [] reasonAt [] (id 2) code := by
  apply BuiltinCalls.Typed.tree_of_functions native [] rfl descriptor
    (metadata := ⟨by cbv, rfl, rfl, rfl, rfl⟩) rfl rfl (by cbv) (by rfl) _ accepted
  intro codes generated
  change [id 0].mapM (fun argument => SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody 2 compilation source [] argument reasonAt) = .ok codes at generated
  cases head : SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody 2 compilation source [] (id 0) reasonAt with
  | error error => simp [head, bind, Except.bind] at generated
  | ok child =>
    simp [head, bind, Except.bind, pure, Except.pure] at generated
    subst codes
    exact DataExpressionSequence.Tree.single (source := source) (node := literalNode) (by rfl) (literalTree native head)
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ []
private def functions : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def identities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem faithful : DataEquality.IdentityFaithful identities :=
  ⟨fun impossible => False.elim impossible, fun impossible => False.elim impossible⟩
private theorem functionLeaves : CompatibleEquality.FunctionObservations checked.catalog functions identities := fun impossible => False.elim impossible
private theorem functionTypes : FunctionRuntimeViews functions := fun impossible => False.elim impossible
private def model := CompatibleAmbientHeap.payloadModel checked values.registry functions
private def faults : FunctionCalls.FaultRep := fun _ _ => True
private theorem valid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, Context.ofSignatures]
  · intro requirement member; cases member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; cases member
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem sourceTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source [] ⟨[]⟩ (id 2) (.value (.integer 7)) ⟨[]⟩ :=
  BuiltinCalls.source_intro (checked := checked) (type := .integer) ⟨by cbv, rfl, rfl, rfl, rfl⟩ rfl
    (.apply (.cons (.intro (lookupExpression?_sound (node := literalNode) (by rfl))
      (.literal rfl (.word (numericLiteralValue?_sound (by rfl)))) .nil) .nil) (.value (.builtin (.wordToInteger (Word.ofNatModulo 7)))))

/-- Actual compiled code composes literal and builtin meaning, with arbitrary
well typed administrative captures admitted in the actual environment. -/
theorem accepted_preserves (native : SourceCoreGeneralFunctions.CallableContext)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.builtin .wordToInteger))
    {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody 3 compilation source [] (id 2) reasonAt = .ok code)
    {actual : Environment} {actualContext : Core.Context}
    (typed : RuntimeEnvironmentHasTypes [] actual actualContext ambient.definitions) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual [] (code.expression.rename Renaming.id) value finalStore ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld .integer code.type faults (.value (.integer 7)) value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld ⟨[]⟩ finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends [] finalWorld ∧
      AdministrativePreserved [] [] finalMap finalStore ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ ⟨[]⟩ :=
  BuiltinCalls.Typed.preserves (values := values) (faults := faults) (node := callNode) functions (.refl _) faithful functionLeaves functionTypes program [] valid unique
    (by intros; trivial) (by intros; trivial) (certified native descriptor accepted) (by cbv)
    (.nil .nil) (.empty) .nil (by intro _ _ absent; cases absent) typed sourceTrace

/-- Completion alone produces the independent Source call and its final heap. -/
theorem accepted_reflects (native : SourceCoreGeneralFunctions.CallableContext)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.builtin .wordToInteger))
    {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody 3 compilation source [] (id 2) reasonAt = .ok code)
    {actual : Environment} {actualContext : Core.Context} {value : Value} {finalStore : Store}
    (typed : RuntimeEnvironmentHasTypes [] actual actualContext ambient.definitions)
    (completed : Evaluates actual [] (code.expression.rename Renaming.id) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context [] source [] ⟨[]⟩ (id 2) outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld .integer code.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends [] finalWorld ∧
      AdministrativePreserved [] [] finalMap finalStore ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ after :=
  BuiltinCalls.Typed.reflects (values := values) (node := callNode) (faults := faults) functions (.refl _) faithful functionLeaves functionTypes program [] valid
    (by intros; trivial) (by intros; trivial) (certified native descriptor accepted) (by cbv)
    (.nil .nil) (.empty) .nil (by intro _ _ absent; cases absent) typed completed

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function choose(m: mapping((Bool, Bool) => Word)) returns (integer) { return wordToInteger(m[(true, false)]); }",
    "function lazy() returns (integer) { let m: mapping((Bool, Bool) => Word); return wordToInteger(m[(true, false)]); }",
    "function paired(a: integer, b: integer) returns (integer) { return integerSub(true ? a : b, false ? a : b); }",
    "function skipped(a: integer) returns (integer) { let missing: Bool; let m: mapping((Bool, Bool) => Word); return wordToInteger((false && missing) ? m[(true, false)] : 7); }",
    "function failed() returns (integer) { let missing: Bool; let m: mapping((Bool, Bool) => Word); return wordToInteger(m[(true, missing)]); }"]}]}

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "typed builtin source checker" (checkProgram workspace)
  let pair : SourceCoreExecution.Value := .product (.bool true) (.bool false)
  let mapping : SourceCoreExecution.Value := .mapping (.product .bool .bool) .word [(pair, .word (Word.ofNatModulo 37)), (pair, .word (Word.ofNatModulo 99))]
  let cases : List (String × List SourceCoreExecution.Value × SourceCoreExecution.Value) := [
    ("choose", [mapping], .integer 37), ("lazy", [], .integer 0),
    ("paired", [.integer (-9), .integer 4], .integer (-13)), ("skipped", [.integer 99], .integer 7)]
  for (name, inputs, expected) in cases do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    SourceCompilerFeatureSupport.require ((← entry.run inputs) == expected) "typed builtin general argument result/effects changed"
    entry.checkResume inputs expected
  let failed ← SourceCompilerFeatureSupport.compileNamed checked "failed"
  let invocation ← failed.invoke []
  match invocation.outcome with
  | .failed reason _ =>
    SourceCompilerFeatureSupport.require ((← invocation.diagnostic reason).isSome) "builtin argument fault lost its diagnostic"
  | _ => throw (IO.userError "builtin argument fault unexpectedly completed")
  IO.println "typed builtin calls: concrete General arguments, meaning/reflection, first duplicate, lazy read, short circuit and fault GREEN"
end Tests.SourceCoreTypedBuiltinCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreTypedDataExpressionSequence
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreTypedDefaultMatchContinuations
/-! Default-backed match stopping composes with the existing block/if receipts.
The source table, typed case order and merged control summary remain explicit.
No-default stopping stays typed and pointwise. Native child grades and suffix
provenance are consumed by the existing helpers, never fields of a receipt. -/
set_option autoImplicit false
namespace Tests.SourceCoreTypedDefaultMatchContinuations
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open ReachableStatementContinuations CoreProof

section Formal
variable {source : TypedSource} {id : StatementId} {node : StatementNode}
  {resolution : MatchResolution} {fallback : List StatementId}
  {control : ControlContext} {context defaultFinal : SourceSemantics.Context}
  {scrutineeType : TypeSystem.Ty} {caseFacts : List BodyFacts} {defaultFacts : BodyFacts} {summary : ControlSummary}

theorem typed_default_stop
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (present : resolution.defaultBody = some fallback)
    (casesTyped : MatchCasesHaveType source control context scrutineeType resolution.cases caseFacts)
    (defaultTyped : StatementsHaveType source control context fallback defaultFinal defaultFacts)
    (merged : mergeBodyControls caseFacts (some defaultFacts) = some summary)
    (arms : ∀ arm fact, (arm, fact) ∈ resolution.cases.zip caseFacts → StoppingStatements source arm.body fact.control)
    (defaultStops : StoppingStatements source fallback defaultFacts.control) :
    StoppingStatement source id summary.eraseValue :=
  .matchDefault found form present casesTyped defaultTyped merged arms defaultStops

theorem concrete_returning_default
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (present : resolution.defaultBody = some fallback)
    (casesTyped : MatchCasesHaveType source control context scrutineeType resolution.cases caseFacts)
    (defaultTyped : StatementsHaveType source control context fallback defaultFinal defaultFacts)
    (merged : mergeBodyControls caseFacts (some defaultFacts) = some summary)
    (armReturns : ∀ arm fact, (arm, fact) ∈ resolution.cases.zip caseFacts →
      ∃ returned returnNode expression, arm.body = [returned] ∧ source.lookupStatement? returned = some returnNode ∧
        returnNode.form = .returnStmt (some expression) ∧ fact.control = .returned)
    {returned : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (defaultBody : fallback = [returned]) (defaultFound : source.lookupStatement? returned = some returnNode)
    (defaultForm : returnNode.form = .returnStmt (some expression)) (defaultControl : defaultFacts.control = .returned) :
    StoppingStatement source id summary.eraseValue := by
  apply typed_default_stop found form present casesTyped defaultTyped merged
  · intro arm fact member
    obtain ⟨returned, returnNode, expression, body, found, form, same⟩ := armReturns arm fact member
    rw [body, same]
    exact .stop (.returnValue found form)
  · rw [defaultBody, defaultControl]
    exact .stop (.returnValue defaultFound defaultForm)

theorem default_in_block {block : StatementId} {blockNode : StatementNode} {dead : List StatementId}
    (found : source.lookupStatement? block = some blockNode) (form : blockNode.form = .block (id :: dead))
    (matchStops : StoppingStatement source id summary) :
    StoppingStatement source block summary.eraseValue :=
  .block found form (.stop matchStops)

theorem default_in_if {conditional : StatementId} {conditionalNode : StatementNode} {condition : ExpressionId}
    {left right : List StatementId} {leftSummary rightSummary : ControlSummary}
    (found : source.lookupStatement? conditional = some conditionalNode)
    (form : conditionalNode.form = .ifThen condition left (some right))
    (leftStops : StoppingStatements source left leftSummary) (rightStops : StoppingStatements source right rightSummary) :
    StoppingStatement source conditional (.branches leftSummary rightSummary) :=
  .conditional found form leftStops rightStops

theorem origin_default_transport {origin : TypedSource} {statements : List StatementId}
    (identity : GenericLexicalStatements.StatementSourceIdentity origin source)
    (stops : StoppingStatements origin statements summary) (unique : NodeOccurrencesUnique source) :
    ListTerminates source statements :=
  GenericLexicalStatements.Stopped.list_terminates unique identity stops

theorem default_source_head {rest : List StatementId} {program : SourceSemantics.Program} {evidence : Dynamic.EvidenceEnvironment}
    {finalContext : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (mode : Bool) (unique : NodeOccurrencesUnique source) (stops : StoppingStatement source id summary)
    (trace : ScalarStatementViews.ListExecutes mode program context evidence source environment before
      (id :: rest) finalContext outcome after) :
    Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after ∧ Dynamic.TerminalControl outcome :=
  source_stopped_head mode unique stops trace

theorem default_source_fault {rest : List StatementId} {program : SourceSemantics.Program} {evidence : Dynamic.EvidenceEnvironment}
    {finalContext : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (mode : Bool) (unique : NodeOccurrencesUnique source) (stops : StoppingStatement source id summary)
    (trace : ScalarStatementViews.ListFaults mode program context evidence source environment before
      (id :: rest) finalContext reason after) :
    finalContext = context ∧ Dynamic.StatementFaults program context evidence source environment before id reason after :=
  source_stopped_fault mode unique stops trace

theorem no_stopping_nil : ¬ StoppingStatements source [] summary := by
  intro stopped
  exact stopped.nonempty rfl
end Formal

abbrev no_default_universal := @Tests.SourceCoreReachableImperativeMatchStatements.no_default_match_has_no_stopping_head

abbrev original_native_return := @Tests.SourceCoreReachableStatementContinuations.concrete_return_stops
abbrev original_native_fault := @Tests.SourceCoreReachableStatementContinuations.concrete_fault_stops

private def content : String := String.intercalate "\n" [
  "enum Choice { Left(Word), Right(Word) }",
  "function nestedDefault(seed: Word) returns (Word) { { match (seed) { case 0 { return 19; } default { return 23; } } } let gap: Word; gap; }",
  "function nestedIf(seed: Word) returns (Word) { if (seed == 0) { match (seed) { case 0 { return 29; } default { return 31; } } } else { return 37; } let gap: Word; gap; }",
  "function deep(seed: Word) returns (Word) { { match (seed) { case 0 { return 47; } default { { match (seed + 1) { case 2 { return 41; } default { return 43; } } } } } } return 99; }",
  "function prefix(seed: Word) returns (Word) { let stamp = 53; { match (seed) { case 0 { let gap: Word; return gap; } default { return 59; } } } let dead = 99; return dead; }",
  "function unit(seed: Word) returns (Unit) { { match (seed) { case 0 { return; } default { return; } } } let gap: Word; gap; }",
  "function ordinary(seed: Word) returns (Word) { match (seed) { case 0 {} default { return 71; } } return 67; }",
  "function noDefault(value: Choice) returns (Word) { match (value) { case .Left(x) { return x; } case .Right(y) { return y; } } }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostic ← match prepared.base.diagnostics with
    | none => throw (IO.userError "typed default match diagnostics missing")
    | some diagnostic => pure diagnostic.program
  let diagnostic := match prepared.base.callableContext with
    | none => diagnostic | some native => {diagnostic with rootTable := native.diagnostics.rootTable}
  let parents ← get "typed default match contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut defaults := 0
  let mut noDefaults := 0
  let mut suffixes := 0
  let mut emptySuffixes := 0
  for named in prepared.base.functions do
    let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
    let own ← match diagnostic.base.find? named.signature.key with
      | none => throw (IO.userError "typed default match own diagnostics missing")
      | some own => pure own
    let source := CallableIndexedNamedGeneration.source named
    let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
    let reasonAt := diagnostic.reasonAt named.signature.key
    let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
      prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostic
      (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext none none
    let policy : SourceCoreLoops.Policy := {
      actual.loopsWithSourceCells actual.expressions.sourceCells named.specialized.function.solvedRequirements
        own.assignments diagnostic named.signature.key lower with
      sourceCells := actual.expressions.sourceCells
      lowerBinder := SourceCoreGeneralFunctions.contextualBinder actual prepared.base.locals named.signature.key [] }
    let statements ← get "typed default match actual roots"
      (source.roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
        | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
    let body ← get "typed default match actual body"
      (SourceCoreLoops.lowerStatementsWithPolicy policy prepared.fuel source scope statements
        named.signature.resultType reasonAt own.fellThroughReason own.table.escapedReason)
    let cached ← get "typed default match cached body"
      (CallableIndexedNamedGeneration.bodyAction prepared named diagnostic parents own statements)
    require (body == cached) "typed default match changed actual body"
    for item in source.nodes do
      match item with
      | .statement node =>
        match node.form with
        | .matchWith resolution =>
          if resolution.defaultBody.isSome then defaults := defaults + 1 else noDefaults := noDefaults + 1
        | _ => pure ()
      | _ => pure ()
    match statements with
    | id :: rest =>
      let node ← match source.lookupStatement? id with
        | none => throw (IO.userError "typed default match root lookup missing") | some node => pure node
      let rootSequence := match node.form with
        | .block _ | .ifThen _ _ (some _) | .matchWith _ => true
        | _ => false
      if rootSequence then
        let whole ← get "typed default match whole flow"
          (SourceCoreLoops.lowerFlowStatementsWithPolicy policy prepared.fuel source scope statements
            named.signature.resultType reasonAt true own.table.escapedReason)
        let childFuel := prepared.fuel - 1
        let suffix ← get "typed default match issued suffix"
          (SourceCoreLoops.lowerFlowStatementsWithPolicy policy childFuel source scope rest
            named.signature.resultType reasonAt true own.table.escapedReason)
        let head ← match node.form with
          | .block inner =>
            get "typed default match inner block"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy childFuel source scope inner
                named.signature.resultType reasonAt false own.table.escapedReason)
          | .ifThen condition left (some right) => do
            let test ← get "typed default match condition" (lower childFuel source scope condition reasonAt)
            let leftCode ← get "typed default match left"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy childFuel source scope left
                named.signature.resultType reasonAt false own.table.escapedReason)
            let rightCode ← get "typed default match right"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy childFuel source scope right
                named.signature.resultType reasonAt false own.table.escapedReason)
            pure (LocalLoop.conditional named.signature.resultType test.expression leftCode rightCode)
          | .matchWith resolution => do
            let callback ← match policy.lowerMatch with
              | none => throw (IO.userError "typed default match callback missing") | some callback => pure callback
            get "typed default match callback"
              (callback policy.lowerExpression
                (fun _ childSource childScope childStatements resultType childReasonAt escaped =>
                  SourceCoreLoops.lowerFlowStatementsWithPolicy policy childFuel childSource childScope childStatements
                    resultType childReasonAt false escaped)
                childFuel source scope id resolution named.signature.resultType reasonAt own.table.escapedReason)
          | _ => pure whole
        match node.form with
        | .block _ | .ifThen _ _ (some _) | .matchWith _ =>
          require (whole == LocalLoop.sequence named.signature.resultType head suffix)
            "typed default match lost full original suffix code"
          if rest.isEmpty then emptySuffixes := emptySuffixes + 1 else suffixes := suffixes + 1
        | _ => pure ()
    | [] => pure ()
  require (defaults == 7 && noDefaults == 1 && suffixes == 5 && emptySuffixes == 1)
    s!"typed default match fixture coverage changed {defaults}/{noDefaults}/{suffixes}/{emptySuffixes}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "typed default match public resume" (first.resume 300000)).observation

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "typed default match continuations" content
    ["nestedDefault", "nestedIf", "deep", "prefix", "unit", "ordinary", "noDefault"]
  inspect compiled
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 811)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("nestedDefault", [w 0], w 19, [(.word, some (w 0)), (.word, some (w 0))]),
    ("nestedDefault", [w 1], w 23, [(.word, some (w 1)), (.word, some (w 1))]),
    ("nestedIf", [w 0], w 29, [(.word, some (w 0)), (.word, some (w 0))]),
    ("nestedIf", [w 1], w 37, [(.word, some (w 1))]),
    ("deep", [w 0], w 47, [(.word, some (w 0)), (.word, some (w 0))]),
    ("deep", [w 1], w 41, [(.word, some (w 1)), (.word, some (w 1)), (.word, some (w 2))]),
    ("deep", [w 2], w 43, [(.word, some (w 2)), (.word, some (w 2)), (.word, some (w 3))]),
    ("prefix", [w 1], w 59, [(.word, some (w 1)), (.word, some (w 53)), (.word, some (w 1))]),
    ("unit", [w 0], .unit, [(.word, some (w 0)), (.word, some (w 0))]),
    ("unit", [w 1], .unit, [(.word, some (w 1)), (.word, some (w 1))]),
    ("ordinary", [w 0], w 67, [(.word, some (w 0)), (.word, some (w 0))]),
    ("ordinary", [w 1], w 71, [(.word, some (w 1)), (.word, some (w 1))])]
  for (name, arguments, expected, cells) in successes do
    let baseline ← finish compiled name arguments 300000 initial
    for fuel in [0, 31, 300000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"typed default match resume changed {name}"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr expected) s!"typed default match result changed {name}"
        require (reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          s!"typed default match full cells/dead suffix changed {name}"
      | other => throw (IO.userError s!"typed default match expected done {name}: {reprStr other}")
  let baseline ← finish compiled "prefix" [w 0] 300000 initial
  for fuel in [0, 31, 300000] do
    let observed ← finish compiled "prefix" [w 0] fuel initial
    require (reprStr observed == reprStr baseline) "typed default match first fault resume changed"
    match observed with
    | .fault (.uninitializedLocal _) final =>
      require (reprStr final.heap == reprStr (initial.heap ++ [⟨.word, some (w 0)⟩, ⟨.word, some (w 53)⟩, ⟨.word, some (w 0)⟩, ⟨.word, none⟩]))
        "typed default match first fault full cells changed"
    | other => throw (IO.userError s!"typed default match expected fault: {reprStr other}")
  let choice ← match compiled.indexed.base.sourceProgram.signatures.dataTypes.find? (·.name == "Choice") with
    | none => throw (IO.userError "typed default match nominal missing") | some choice => pure choice
  let sourceType := TypeSystem.Ty.nominal choice.id []
  for (index, payload) in [(0, 73), (1, 79)] do
    let metadata : DataConstructorInstantiation := ⟨⟨choice.id, index⟩, [], [.word], sourceType⟩
    let argument : SourceTypedRuntime.Value := .constructed metadata [w payload]
    let baseline ← finish compiled "noDefault" [argument] 300000 initial
    for fuel in [0, 31, 300000] do
      let observed ← finish compiled "noDefault" [argument] fuel initial
      require (reprStr observed == reprStr baseline) "typed no-default public resume changed"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr (w payload)) "typed no-default nominal result changed"
        require (reprStr final.heap == reprStr (initial.heap ++ [⟨sourceType, some argument⟩, ⟨sourceType, some argument⟩, ⟨.word, some (w payload)⟩]))
          "typed no-default nominal full cells changed"
      | other => throw (IO.userError s!"typed no-default expected done: {reprStr other}")
  IO.println "typed default match continuations: nested block/if, actual issued suffix, typed no-default separate, full cells/fault/resume GREEN"

end Tests.SourceCoreTypedDefaultMatchContinuations
end

section
-- leanmerge: from Solcore.Test.SourceCoreTypedForHeader
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual for-item lowering, whole native typing and an independent source
header trace feed the concrete post theorems. Runtime fixtures preserve mixed
header allocations, post scopes, transfers, fault effects and resumption. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreTypedForHeader
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedForHeader GeneralHeap CompatiblePayload CompatibleEquality ReadOnly
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"assignment_statement", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "assignment_statement.solc"⟩, 0, 1⟩
private def expression : ExpressionId := ⟨⟨owner, 0⟩⟩
private def statement (n : Nat) : StatementId := ⟨⟨owner, n + 1⟩⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "x", .mono .bool, [], false, none⟩
private def assignment : AssignmentResolution := ⟨⟨binder.id, [], .bool⟩, []⟩
private def literal : ExpressionNode := { id := expression, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def assigned : StatementNode := ⟨statement 0, span, .unit, .assignValue assignment .equal expression⟩
private def returned : StatementNode := ⟨statement 1, span, .bool, .returnStmt (some expression)⟩
private def breakNode : StatementNode := ⟨statement 2, span, .unit, .breakStmt⟩
private def loopNode : StatementNode := ⟨statement 3, span, .unit, .whileLoop expression [statement 0, statement 2]⟩
private def statements := [statement 3, statement 1]
private def source : TypedSource := {
  owner := owner
  inputs := [binder]
  roots := statements.map .statement
  nodes := [.expression literal, .statement assigned, .statement returned, .statement breakNode, .statement loopNode]
}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def environment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def before : Dynamic.Heap := ⟨[{type := .bool, value := none}]⟩
private def after : Dynamic.Heap := ⟨[{type := .bool, value := some (.bool true)}]⟩
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem booleanTyped : ExpressionHasType source context expression .bool := by
  have admissible : TypeAdmissible context .bool := .bool (by
    simp [TypeParameterBindersWellFormed, context, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal])
  apply ExpressionHasType.ofOrdinary (node := literal) (rawType := .bool) (lookupExpression?_sound rfl)
    (.reference (.builtinBoolean true)) admissible admissible
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem writable : WritableLocal context binder.id .bool := by
  apply WritableLocal.withLocal_mono_admissible
  exact .bool (by simp [TypeParameterBindersWellFormed, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal])
private theorem booleanSyntax : CompatibleExpressionTyped.Syntax source expression :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := literal) rfl (.bool _ _)))))))
private def items : List ForItemForm := [.expression expression, .assignValue assignment .equal expression]
private theorem syntaxTree : TypedForHeader.Syntax source context items := by
  apply TypedForHeader.Syntax.discard (expressionNode := literal) rfl booleanTyped booleanSyntax
  apply TypedForHeader.Syntax.assign
  · intro actual found
    have expected : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder := rfl
    have same := Except.ok.inj (expected.symm.trans found)
    cases same
    exact .nil _
  · intro actual found
    have expected : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder := rfl
    have same := Except.ok.inj (expected.symm.trans found)
    cases same
    exact writable
  · exact booleanTyped
  · exact .inl rfl
  · exact .nil

private theorem sourceAssigned : Dynamic.SourcePlaceAssignment program context [] source (Dynamic.AssignmentValueApplies .equal)
    environment before assignment.target expression (.bool true) after := by
  have read : Dynamic.Heap.Reads before ⟨0⟩ {type := .bool, value := none} := .intro .head
  have initial : Dynamic.RootInitialValue {type := .bool, value := none} none :=
    .uninitialized (by rintro ⟨key, value, impossible⟩; cases impossible)
  refine .intro (targetHeap := before) (rhsHeap := before) (rightValue := .bool true)
    (target := ⟨⟨0⟩, .bool, .bool, [], none⟩) ?_ ?_ ?_
  · exact Dynamic.SourcePlaceResolves.intro (place := assignment.target) (environment := environment) .head read .nil read initial .nil
  · exact .intro (node := literal) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil
  · exact .intro read rfl initial (.leaf (.equal none (.bool true))) (.intro read .head)

private theorem sourceTrace : Dynamic.ForItemsExecute program context [] source environment before items context environment after :=
  .cons (.expression (.intro (node := literal) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil))
    (.cons (.assignValue sourceAssigned) .nil)

section CompilerBridge
variable {layouts : SourceCoreAllocationLayouts.Prepared} {specialization : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {definitions : DataEnvironment}
  {policy : SourceCoreLoops.Policy}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {missingReason : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  (matched : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingReason)
  (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
  (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt specialization active onError)))
  (sourceSignatures : context.signatures = values.checked.signatures)
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  (expressions : ∀ sourceContext scope fuel id lowered,
    sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
    sourceContext.signatures = values.checked.signatures →
    CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
    policy.lowerExpression fuel source scope id reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? id = some node ∧ CompatibleExpressionTyped.Tree readFuel values source sourceContext solved reasonAt scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
  {fuel : Nat} {site : SourceCoreElaboration.ErrorSite} {code : Expr} {nativeType : Ty}
  (accepted : SourceCoreLoops.lowerForItems policy site fuel source scope items .bool reasonAt
    (fun _ => .ok (LocalLoop.fallthrough .bool)) = .ok code)
  (nativeTyped : infer? (SourceCoreLocalCell.coreContext scope ++ administrative) code definitions = some nativeType)

include matched binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped in
/-- Static child extraction and one actual checker receipt determine every
allocation/assignment header node; no child evaluation is a premise. -/
theorem certified : Tree layouts specialization active frame globals onError readFuel values source solved reasonAt definitions administrative
    .bool (Fallthrough .bool) context scope items code := by
  exact tree_of_lowerForItems binderPolicy allocationPolicy matched unique expressions
    (fun _ _ _ _ _ _ _ accepted => Except.ok.inj accepted.symm) syntaxTree rfl rfl sourceSignatures declarations
      accepted (infer_sound nativeTyped)

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (sameDefinitions : definitions = ambient.definitions)
  (layoutDefinitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (valid : CompatibleExpressionLiterals.ContextValid solved context []) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  (errors : Tree.Errors registry faults (certified matched binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped))
  {mapping : LocationMap} {world : StoreTyping} {canonical actual : Environment} {actualContext : Core.Context}
  {store : Store} {ξ : Renaming} {location : Location} {native : CallableIndexedHistory.NativeFrame}
  (environments : DataHeap.EnvRepresents (storageCatalog values.checked.catalog) mapping world administrative scope environment canonical ambient.definitions)
  (heaps : CompatibleHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type location))
  (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode frame native))
  (unmapped : location ∉ mapping)

include matched binderPolicy allocationPolicy sourceSignatures declarations expressions nativeTyped sameDefinitions layoutDefinitions registered extension valid uninitialized missing faithful observations errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_post_restores :
    ∃ tail : Tail registry functions source solved [] administrative frame globals location native (Fallthrough .bool) context environment after,
      Evaluates actual store (code.rename ξ) (LocalLoop.fallthroughValue .bool) tail.store ∧
      CompatibleHeap.HeapRepresents values.checked registry functions tail.mapping tail.world after tail.store ∧
      DataHeap.EnvRepresents (storageCatalog values.checked.catalog) tail.mapping tail.world administrative scope environment canonical ambient.definitions ∧
      Dynamic.EnvironmentAgrees after context.locals environment ∧
      RuntimeEnvironmentHasTypes tail.world actual actualContext ambient.definitions := by
  subst definitions
  obtain ⟨tail, maps, worlds, preservation, metadata, evaluated, outer, restored, actualTyped⟩ :=
    (certified matched binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped).preserves_post
      functions layoutDefinitions registered extension program [] uninitialized missing faithful observations
      valid unique environments heaps locals agrees typed reference read unmapped sourceTrace
  exact ⟨tail, evaluated, tail.heaps, outer, restored, actualTyped⟩

include matched binderPolicy allocationPolicy sourceSignatures declarations expressions nativeTyped sameDefinitions layoutDefinitions registered extension valid uninitialized missing faithful observations errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_post_reflects (runtimeViews : FunctionRuntimeViews functions) {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    Result registry functions program source solved [] administrative frame globals location native .bool faults (Fallthrough .bool)
      context environment before items mapping world store value finalStore := by
  subst definitions
  exact (certified matched binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped).reflects
    functions layoutDefinitions registered extension program [] uninitialized missing faithful observations runtimeViews
    errors valid unique environments heaps locals agrees typed reference read unmapped completed

include matched binderPolicy allocationPolicy sourceSignatures declarations expressions nativeTyped sameDefinitions layoutDefinitions registered extension valid uninitialized missing faithful observations errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_post_shape (runtimeViews : FunctionRuntimeViews functions) {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    value = LocalLoop.fallthroughValue .bool ∨ ∃ token, value = .inLeft (LocalLoop.controlType .bool) (.word token) := by
  subst definitions
  rcases (certified matched binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped).reflects_post
      functions layoutDefinitions registered extension program [] uninitialized missing faithful observations runtimeViews
      errors valid unique environments heaps locals agrees typed reference read unmapped completed with done | fault
  · obtain ⟨_, _, _, _, _, same, _⟩ := done
    exact .inl same
  · obtain ⟨_, _, token, _, _, _, _, same, _⟩ := fault
    exact .inr ⟨token, same⟩
end CompilerBridge

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function mixed() returns (Word) { let sum = 0; for (let i: Word, i = 0, let flag: Bool = true; i < 3; let copy = i, i = copy + 1) { if (flag) { sum += i; } } return sum; }",
    "function shadow() returns (Word) { let i = 17; for (let i = 0; i < 2; let copy = i, i = copy + 1) { continue; } return i; }",
    "function falseFirst() returns (Word) { for (let i = 5; false; let never = 99) { return 0; } return 5; }",
    "function breaks() returns (Word) { for (let i = 0; true; let never = 99) { break; } return 1; }",
    "function returns() returns (Word) { for (let i = 0; true; let never = 99) { return i; } return 1; }",
    "function initializerFault() returns (Word) { let missing: Word; let seen: mapping(Bool => Word); for (let ready = 1, let dead = seen[false] + missing; true; ) { return 0; } return 1; }",
    "function postFault() returns (Word) { let missing: Word; let seen: mapping(Bool => Word); for (let i = 0; true; let copy = i, i = seen[false] + missing, let never = 99) { continue; } return 1; }",
    "function postAbsent() returns (Word) { for (let i = 0; true; let absent: Word, i = absent) { continue; } return 1; }"
  ]}] }
private def escape : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function main() returns (Word) { for (let i = 0; false; let copy = i) { } return copy; }"}] }
private def failureResume (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let complete ← entry.invoke []
  let token ← match complete.outcome with
    | .failed token _ => pure token
    | _ => throw (IO.userError "header fixture unexpectedly succeeded")
  SourceCompilerFeatureSupport.require (← complete.diagnostic token).isSome "header failure lost its diagnostic"
  for fuel in [0, 10, 35, 100] do
    let started ← SourceCompilerFeatureSupport.get "header suspension"
      (← complete.initial.run complete.key [] {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed, complete.outcome with
    | .failed actual heap, .failed expected initial =>
        SourceCompilerFeatureSupport.require (actual == expected && heap.heapSize == initial.heapSize)
          "header resume changed fault or allocated after failure"
    | _, _ => throw (IO.userError "header resume changed outcome")

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "for header checker" (checkProgram workspace)
  for (name, result) in [("mixed", 3), ("shadow", 17), ("falseFirst", 5), ("breaks", 1), ("returns", 0)] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    let expected := SourceCompilerFeatureSupport.scalar result
    SourceCompilerFeatureSupport.require ((← entry.run []) == expected) s!"{name}: for header value changed"
    entry.checkResume [] expected
  let mixed ← SourceCompilerFeatureSupport.compileNamed checked "mixed"
  mixed.checkCells [] [(.word, some (SourceCompilerFeatureSupport.scalar 3)), (.word, some (SourceCompilerFeatureSupport.scalar 3)),
    (.bool, some (.bool true)), (.word, some (SourceCompilerFeatureSupport.scalar 0)),
    (.word, some (SourceCompilerFeatureSupport.scalar 1)), (.word, some (SourceCompilerFeatureSupport.scalar 2))]
  let shadow ← SourceCompilerFeatureSupport.compileNamed checked "shadow"
  shadow.checkCells [] [(.word, some (SourceCompilerFeatureSupport.scalar 17)), (.word, some (SourceCompilerFeatureSupport.scalar 2)),
    (.word, some (SourceCompilerFeatureSupport.scalar 0)), (.word, some (SourceCompilerFeatureSupport.scalar 1))]
  for (name, stored) in [("falseFirst", 5), ("breaks", 0), ("returns", 0)] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    entry.checkCells [] [(.word, some (SourceCompilerFeatureSupport.scalar stored))]
  let initializer ← SourceCompilerFeatureSupport.compileNamed checked "initializerFault"
  failureResume initializer
  initializer.checkCells [] [(.word, none), (.mapping .bool .word, some (.mapping .bool .word [])),
    (.word, some (SourceCompilerFeatureSupport.scalar 1))]
  let post ← SourceCompilerFeatureSupport.compileNamed checked "postFault"
  failureResume post
  post.checkCells [] [(.word, none), (.mapping .bool .word, some (.mapping .bool .word [])),
    (.word, some (SourceCompilerFeatureSupport.scalar 0)), (.word, some (SourceCompilerFeatureSupport.scalar 0))]
  let absent ← SourceCompilerFeatureSupport.compileNamed checked "postAbsent"
  failureResume absent
  absent.checkCells [] [(.word, some (SourceCompilerFeatureSupport.scalar 0)), (.word, none)]
  SourceCompilerFeatureSupport.require (checkProgram escape).toOption.isNone "post local escaped its lexical scope"
  IO.println "typed for headers: mixed allocations, post scope restoration, transfer ordering, fault effects and resume GREEN"

end Tests.SourceCoreTypedForHeader
end

section
-- leanmerge: from Solcore.Test.SourceCoreTypedImperative
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Assignment inside while consumes actual lowering and whole-code typing,
with an independent source trace. Runtime fixtures exercise repeated/nested
iterations, scoped allocations, transfers, fault ordering and resumption. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreTypedImperative
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedImperative GeneralHeap CompatiblePayload CompatibleEquality ReadOnly
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"assignment_statement", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "assignment_statement.solc"⟩, 0, 1⟩
private def expression : ExpressionId := ⟨⟨owner, 0⟩⟩
private def statement (n : Nat) : StatementId := ⟨⟨owner, n + 1⟩⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "x", .mono .bool, [], false, none⟩
private def assignment : AssignmentResolution := ⟨⟨binder.id, [], .bool⟩, []⟩
private def literal : ExpressionNode := { id := expression, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def assigned : StatementNode := ⟨statement 0, span, .unit, .assignValue assignment .equal expression⟩
private def returned : StatementNode := ⟨statement 1, span, .bool, .returnStmt (some expression)⟩
private def breakNode : StatementNode := ⟨statement 2, span, .unit, .breakStmt⟩
private def loopNode : StatementNode := ⟨statement 3, span, .unit, .whileLoop expression [statement 0, statement 2]⟩
private def statements := [statement 3, statement 1]
private def source : TypedSource := {
  owner := owner
  inputs := [binder]
  roots := statements.map .statement
  nodes := [.expression literal, .statement assigned, .statement returned, .statement breakNode, .statement loopNode]
}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def environment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def before : Dynamic.Heap := ⟨[{type := .bool, value := none}]⟩
private def after : Dynamic.Heap := ⟨[{type := .bool, value := some (.bool true)}]⟩
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem booleanTyped : ExpressionHasType source context expression .bool := by
  have admissible : TypeAdmissible context .bool := .bool (by
    simp [TypeParameterBindersWellFormed, context, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal])
  apply ExpressionHasType.ofOrdinary (node := literal) (rawType := .bool) (lookupExpression?_sound rfl)
    (.reference (.builtinBoolean true)) admissible admissible
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem writable : WritableLocal context binder.id .bool := by
  apply WritableLocal.withLocal_mono_admissible
  exact .bool (by simp [TypeParameterBindersWellFormed, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal])
private theorem booleanSyntax : CompatibleExpressionTyped.Syntax source expression :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := literal) rfl (.bool _ _)))))))
private theorem syntaxTree (mode : Bool) : TypedImperative.Syntax source context mode statements .bool := by
  apply TypedImperative.Syntax.whileLoop (node := loopNode) (conditionNode := literal) rfl rfl rfl rfl booleanTyped
    booleanSyntax
  · apply TypedImperative.Syntax.assign (node := assigned) rfl rfl
    · intro actual found
      have : SourceCoreCompatibleDataPlaces.rootBinder source binder.id = .ok binder := rfl
      have same := Except.ok.inj (this.symm.trans found)
      cases same
      exact .nil _
    · intro actual found
      have : SourceCoreCompatibleDataPlaces.rootBinder source binder.id = .ok binder := rfl
      have same := Except.ok.inj (this.symm.trans found)
      cases same
      exact writable
    · exact booleanTyped
    · exact .inl rfl
    · exact .breaking (node := breakNode) rfl rfl
  · exact .body (.body (.returnValue [] rfl rfl rfl rfl rfl booleanTyped booleanSyntax))

private theorem sourceAssigned : Dynamic.SourcePlaceAssignment program context [] source (Dynamic.AssignmentValueApplies .equal)
    environment before assignment.target expression (.bool true) after := by
  have read : Dynamic.Heap.Reads before ⟨0⟩ {type := .bool, value := none} := .intro .head
  have initial : Dynamic.RootInitialValue {type := .bool, value := none} none :=
    .uninitialized (by rintro ⟨key, value, impossible⟩; cases impossible)
  refine .intro (targetHeap := before) (rhsHeap := before) (rightValue := .bool true)
    (target := ⟨⟨0⟩, .bool, .bool, [], none⟩) ?_ ?_ ?_
  · exact Dynamic.SourcePlaceResolves.intro (place := assignment.target) (environment := environment) .head read .nil read initial .nil
  · exact .intro (node := literal) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil
  · exact .intro read rfl initial (.leaf (.equal none (.bool true))) (.intro read .head)

private theorem sourceTrace (mode : Bool) : TypedScopedStatements.Executes mode program context [] source environment before
    statements context (.returned (.bool true)) after := by
  have assignedTrace : Dynamic.StatementExecutes program context [] source environment before (statement 0) context (.fallthrough environment) after :=
    .assignValue (lookupStatement?_sound rfl) rfl sourceAssigned
  have loopTrace : Dynamic.StatementExecutes program context [] source environment before (statement 3) context (.fallthrough environment) after := by
    apply Dynamic.StatementExecutes.whileLoop (outcome := .fallthrough environment) (lookupStatement?_sound (node := loopNode) rfl) rfl
    apply Dynamic.WhileExecutes.breaks
    · exact .intro (node := literal) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil
    · exact .cons assignedTrace (.terminal (.breakStmt (lookupStatement?_sound (node := breakNode) rfl) rfl) (.breaking environment))
  have last : Dynamic.StatementExecutes program context [] source environment after (statement 1) context (.returned (.bool true)) after :=
    .returnValue (lookupStatement?_sound rfl) rfl (.intro (node := literal) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil)
  exact TypedScopedStatements.prepend (lookupStatement?_sound (show source.lookupStatement? (statement 3) = some loopNode from rfl))
    (by intro _ _ _ impossible; cases impossible) loopTrace
    (TypedLexicalControl.terminal_outcome program [] (show source.lookupStatement? (statement 1) = some returned from rfl)
      (by intro expression impossible; cases impossible) (.control last) (.returned _))

section CompilerBridge
variable {layouts : SourceCoreAllocationLayouts.Prepared} {specialization : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {definitions : DataEnvironment}
  {policy : SourceCoreLoops.Policy}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {missingReason : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  (matched : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingReason)
  (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
  (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt specialization active onError)))
  (sourceSignatures : context.signatures = values.checked.signatures)
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  (expressions : ∀ sourceContext scope fuel id lowered,
    sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
    sourceContext.signatures = values.checked.signatures →
    CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
    policy.lowerExpression fuel source scope id reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? id = some node ∧ CompatibleExpressionTyped.Tree readFuel values source sourceContext solved reasonAt scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
  {mode : Bool} {fuel : Nat} {selfReason : Word} {code : Expr} {nativeType : Ty}
  (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements .bool reasonAt mode selfReason = .ok code)
  (nativeTyped : infer? (SourceCoreLocalCell.coreContext scope ++ administrative) code definitions = some nativeType)

include matched binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped in
/-- A single whole-code checker receipt supplies both loop typing and the
assignment continuation. The remaining premises are static source certificates. -/
theorem certified : Tree layouts specialization active frame globals onError readFuel values source solved reasonAt definitions administrative
    context scope mode statements .bool .bool code := by
  apply tree_of_typed_flow matched.read binderPolicy allocationPolicy ?_ matched unique expressions
    (syntaxTree mode) rfl rfl sourceSignatures declarations (by rfl) accepted (infer_sound nativeTyped)
  intro sourceContext closed residual signatures scope fuel id node lowered declarations syntaxValue found typed generated
  obtain ⟨_, _, tree, _⟩ := expressions sourceContext scope fuel id lowered closed residual signatures declarations generated
  exact tree

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (sameDefinitions : definitions = ambient.definitions)
  (layoutDefinitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (valid : CompatibleExpressionLiterals.ContextValid solved context []) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  (errors : Tree.Errors registry faults (certified matched binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped))
  {mapping : LocationMap} {world : StoreTyping} {canonical actual : Environment} {actualContext : Core.Context}
  {store : Store} {ξ : Renaming} {location : Location} {native : CallableIndexedHistory.NativeFrame}
  (environments : DataHeap.EnvRepresents (storageCatalog values.checked.catalog) mapping world administrative scope environment canonical ambient.definitions)
  (heaps : CompatibleHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type location))
  (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode frame native))
  (unmapped : location ∉ mapping)

include matched binderPolicy allocationPolicy sourceSignatures declarations expressions nativeTyped sameDefinitions layoutDefinitions registered extension valid uninitialized missing faithful observations errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_preserves :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      TypedLexicalWhile.FlowRep (values := values) (registry := registry) functions finalMap finalWorld faults .bool .bool (.returned (.bool true)) value ∧
      CompatibleHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment context after := by
  subst definitions
  exact (certified matched binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped).preserves functions layoutDefinitions registered extension program []
    uninitialized missing faithful observations errors valid unique environments heaps locals agrees typed reference read unmapped (sourceTrace mode)

include matched binderPolicy allocationPolicy sourceSignatures declarations expressions nativeTyped sameDefinitions layoutDefinitions registered extension valid uninitialized missing faithful observations errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_reflects (runtimeViews : FunctionRuntimeViews functions) {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ finalContext outcome sourceHeap finalMap finalWorld,
      TypedScopedStatements.Executes mode program context [] source environment before statements finalContext outcome sourceHeap ∧
      TypedLexicalWhile.FlowRep (values := values) (registry := registry) functions finalMap finalWorld faults .bool .bool outcome value ∧
      CompatibleHeap.HeapRepresents values.checked registry functions finalMap finalWorld sourceHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before sourceHeap ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext sourceHeap := by
  subst definitions
  exact (certified matched binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped).reflects functions layoutDefinitions registered extension program []
    uninitialized missing faithful observations runtimeViews errors valid unique environments heaps locals agrees typed reference read unmapped completed
end CompilerBridge

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Word) }",
    "function repeated() returns (Word) { let i = 0; let sum: Word; sum = 0; while (i < 5) { i += 1; if (i == 2) { continue; } { let shadow = i; sum += shadow; } if (i == 4) { break; } } return sum; }",
    "function nested() returns (Word) { let i = 0; let m: mapping(Bool => Word); while (i < 3) { let j = 0; while (j < 2) { j += 1; m[true] = i * 10 + j; } i += 1; } return m[true]; }",
    "function early() returns (Word) { let i = 0; while (true) { i += 1; if (i == 3) { return i; } } return 99; }",
    "function rhsFault() returns (Word) { let i = 0; let m: mapping(Bool => Word); let keys: mapping(Bool => Bool); let lazy: mapping(Bool => Word); let missing: Word; while (i < 2) { i += 1; m[keys[true]] = lazy[false] + missing; let never = true; } return 0; }",
    "function targetFault() returns (Word) { let i = 0; let m: mapping(Bool => Box); let keys: mapping(Bool => Bool); let rhs: mapping(Bool => Word); while (i < 2) { i += 1; m[keys[true]] = .Box(rhs[false]); } return 0; }"
  ]}] }
private def failureResume (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let complete ← entry.invoke []
  let token ← match complete.outcome with
    | .failed token _ => pure token
    | _ => throw (IO.userError "assignment fixture unexpectedly succeeded")
  SourceCompilerFeatureSupport.require (← complete.diagnostic token).isSome "assignment failure lost its diagnostic"
  for fuel in [0, 10, 35, 100] do
    let started ← SourceCompilerFeatureSupport.get "assignment suspension"
      (← complete.initial.run complete.key [] {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed, complete.outcome with
    | .failed actual heap, .failed expected initial =>
        SourceCompilerFeatureSupport.require (actual == expected && heap.heapSize == initial.heapSize)
          "assignment resume changed fault or executed unreachable allocation"
    | _, _ => throw (IO.userError "assignment resume changed outcome")

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "imperative checker" (checkProgram workspace)
  for (name, result) in [("repeated", 8), ("nested", 22), ("early", 3)] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    let expected := SourceCompilerFeatureSupport.scalar result
    SourceCompilerFeatureSupport.require ((← entry.run []) == expected) s!"{name}: mixed assignment/loop value changed"
    entry.checkResume [] expected
  let repeated ← SourceCompilerFeatureSupport.compileNamed checked "repeated"
  repeated.checkCells [] [(.word, some (SourceCompilerFeatureSupport.scalar 4)), (.word, some (SourceCompilerFeatureSupport.scalar 8)),
    (.word, some (SourceCompilerFeatureSupport.scalar 1)), (.word, some (SourceCompilerFeatureSupport.scalar 3)), (.word, some (SourceCompilerFeatureSupport.scalar 4))]
  let rhs ← SourceCompilerFeatureSupport.compileNamed checked "rhsFault"
  failureResume rhs
  rhs.checkCells [] [(.word, some (SourceCompilerFeatureSupport.scalar 1)), (.mapping .bool .word, none),
    (.mapping .bool .bool, some (.mapping .bool .bool [])), (.mapping .bool .word, some (.mapping .bool .word [])), (.word, none)]
  let target ← SourceCompilerFeatureSupport.compileNamed checked "targetFault"
  failureResume target
  let cells := (SourceCompilerFeatureSupport.sourceState (← target.audit [])).heap
  SourceCompilerFeatureSupport.require ((match cells with
    | [count, root, _, rhs] => (match count.value with | some (.word value) => value == Word.ofNatModulo 1 | _ => false) && root.value.isNone && rhs.value.isNone
    | _ => false)) "loop target fault executed RHS or lost prior assignment"
  IO.println "typed imperative: assignments inside repeated/nested loops, lexical exits, break/continue/return, fault effects and resume GREEN"
end Tests.SourceCoreTypedImperative
end

section
-- leanmerge: from Solcore.Test.SourceCoreTypedImperativeFor
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Mixed for/while consumes actual lowering and whole-code typing,
with an independent source trace. Runtime fixtures exercise repeated/nested
iterations, scoped allocations, transfers, fault ordering and resumption. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreTypedImperativeFor
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedImperativeFor GeneralHeap CompatiblePayload CompatibleEquality ReadOnly
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"assignment_statement", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "assignment_statement.solc"⟩, 0, 1⟩
private def expression : ExpressionId := ⟨⟨owner, 0⟩⟩
private def statement (n : Nat) : StatementId := ⟨⟨owner, n + 1⟩⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "x", .mono .bool, [], false, none⟩
private def assignment : AssignmentResolution := ⟨⟨binder.id, [], .bool⟩, []⟩
private def literal : ExpressionNode := { id := expression, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def assigned : StatementNode := ⟨statement 0, span, .unit, .assignValue assignment .equal expression⟩
private def returned : StatementNode := ⟨statement 1, span, .bool, .returnStmt (some expression)⟩
private def breakNode : StatementNode := ⟨statement 2, span, .unit, .breakStmt⟩
private def loopNode : StatementNode := ⟨statement 3, span, .unit, .forLoop [.expression expression] expression [.assignValue assignment .equal expression] [statement 0, statement 2]⟩
private def statements := [statement 3, statement 1]
private def source : TypedSource := {
  owner := owner
  inputs := [binder]
  roots := statements.map .statement
  nodes := [.expression literal, .statement assigned, .statement returned, .statement breakNode, .statement loopNode]
}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def environment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def before : Dynamic.Heap := ⟨[{type := .bool, value := none}]⟩
private def after : Dynamic.Heap := ⟨[{type := .bool, value := some (.bool true)}]⟩
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem booleanTyped : ExpressionHasType source context expression .bool := by
  have admissible : TypeAdmissible context .bool := .bool (by
    simp [TypeParameterBindersWellFormed, context, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal])
  apply ExpressionHasType.ofOrdinary (node := literal) (rawType := .bool) (lookupExpression?_sound rfl)
    (.reference (.builtinBoolean true)) admissible admissible
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem writable : WritableLocal context binder.id .bool := by
  apply WritableLocal.withLocal_mono_admissible
  exact .bool (by simp [TypeParameterBindersWellFormed, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal])
private theorem booleanSyntax : CompatibleExpressionTyped.Syntax source expression :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := literal) rfl (.bool _ _)))))))
private theorem assignmentSyntax {rest : List ForItemForm} (remaining : TypedForHeader.Syntax source context rest) :
    TypedForHeader.Syntax source context (.assignValue assignment .equal expression :: rest) := by
  apply TypedForHeader.Syntax.assign
  · intro actual found
    have : SourceCoreCompatibleDataPlaces.rootBinder source binder.id = .ok binder := rfl
    cases Except.ok.inj (this.symm.trans found)
    exact .nil _
  · intro actual found
    have : SourceCoreCompatibleDataPlaces.rootBinder source binder.id = .ok binder := rfl
    cases Except.ok.inj (this.symm.trans found)
    exact writable
  · exact booleanTyped
  · exact .inl rfl
  · exact remaining
private theorem syntaxTree (mode : Bool) : TypedImperativeFor.Syntax source context (.statements mode statements) .bool := by
  apply TypedImperativeFor.Syntax.forLoop (node := loopNode) rfl rfl rfl
  · apply TypedImperativeFor.Syntax.initializerDiscard (expressionNode := literal) rfl booleanTyped booleanSyntax
    apply TypedImperativeFor.Syntax.initializersDone (conditionNode := literal) rfl rfl booleanTyped booleanSyntax
    · apply TypedImperativeFor.Syntax.assign (node := assigned) rfl rfl
      · intro actual found
        have : SourceCoreCompatibleDataPlaces.rootBinder source binder.id = .ok binder := rfl
        cases Except.ok.inj (this.symm.trans found)
        exact .nil _
      · intro actual found
        have : SourceCoreCompatibleDataPlaces.rootBinder source binder.id = .ok binder := rfl
        cases Except.ok.inj (this.symm.trans found)
        exact writable
      · exact booleanTyped
      · exact .inl rfl
      · exact .breaking (node := breakNode) rfl rfl
    · exact assignmentSyntax .nil
  · exact .body (.body (.returnValue [] rfl rfl rfl rfl rfl booleanTyped booleanSyntax))

private theorem sourceAssigned : Dynamic.SourcePlaceAssignment program context [] source (Dynamic.AssignmentValueApplies .equal)
    environment before assignment.target expression (.bool true) after := by
  have read : Dynamic.Heap.Reads before ⟨0⟩ {type := .bool, value := none} := .intro .head
  have initial : Dynamic.RootInitialValue {type := .bool, value := none} none :=
    .uninitialized (by rintro ⟨key, value, impossible⟩; cases impossible)
  refine .intro (targetHeap := before) (rhsHeap := before) (rightValue := .bool true)
    (target := ⟨⟨0⟩, .bool, .bool, [], none⟩) ?_ ?_ ?_
  · exact Dynamic.SourcePlaceResolves.intro (place := assignment.target) (environment := environment) .head read .nil read initial .nil
  · exact .intro (node := literal) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil
  · exact .intro read rfl initial (.leaf (.equal none (.bool true))) (.intro read .head)

private theorem sourceTrace (mode : Bool) : TypedScopedStatements.Executes mode program context [] source environment before
    statements context (.returned (.bool true)) after := by
  have assignedTrace : Dynamic.StatementExecutes program context [] source environment before (statement 0) context (.fallthrough environment) after :=
    .assignValue (lookupStatement?_sound rfl) rfl sourceAssigned
  have loopTrace : Dynamic.StatementExecutes program context [] source environment before (statement 3) context (.fallthrough environment) after := by
    apply Dynamic.StatementExecutes.forLoop (outcome := .fallthrough environment) (lookupStatement?_sound (node := loopNode) rfl) rfl
      (.cons (.expression (.intro (node := literal) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil)) .nil)
    apply Dynamic.ForLoopExecutes.breaks
    · exact .intro (node := literal) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil
    · exact .cons assignedTrace (.terminal (.breakStmt (lookupStatement?_sound (node := breakNode) rfl) rfl) (.breaking environment))
  have last : Dynamic.StatementExecutes program context [] source environment after (statement 1) context (.returned (.bool true)) after :=
    .returnValue (lookupStatement?_sound rfl) rfl (.intro (node := literal) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil)
  exact TypedScopedStatements.prepend (lookupStatement?_sound (show source.lookupStatement? (statement 3) = some loopNode from rfl))
    (by intro _ _ _ impossible; cases impossible) loopTrace
    (TypedLexicalControl.terminal_outcome program [] (show source.lookupStatement? (statement 1) = some returned from rfl)
      (by intro expression impossible; cases impossible) (.control last) (.returned _))

section CompilerBridge
variable {layouts : SourceCoreAllocationLayouts.Prepared} {specialization : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {definitions : DataEnvironment}
  {policy : SourceCoreLoops.Policy}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {missingReason : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  (matched : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingReason)
  (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
  (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt specialization active onError)))
  (sourceSignatures : context.signatures = values.checked.signatures)
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  (expressions : ∀ sourceContext scope fuel id lowered,
    sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
    sourceContext.signatures = values.checked.signatures →
    CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
    policy.lowerExpression fuel source scope id reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? id = some node ∧ CompatibleExpressionTyped.Tree readFuel values source sourceContext solved reasonAt scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
  {mode : Bool} {fuel : Nat} {selfReason : Word} {code : Expr} {nativeType : Ty}
  (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements .bool reasonAt mode selfReason = .ok code)
  (nativeTyped : infer? (SourceCoreLocalCell.coreContext scope ++ administrative) code definitions = some nativeType)

include matched binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped in
/-- A single whole-code checker receipt supplies both loop typing and the
assignment continuation. The remaining premises are static source certificates. -/
theorem certified : Tree layouts specialization active frame globals onError readFuel values source solved reasonAt definitions administrative
    context scope (.statements mode statements) .bool .bool code := by
  apply tree_of_typed_flow matched.read binderPolicy allocationPolicy ?_ matched unique expressions
    (syntaxTree mode) rfl rfl sourceSignatures declarations (by rfl) accepted (infer_sound nativeTyped)
  intro sourceContext closed residual signatures scope fuel id node lowered declarations syntaxValue found typed generated
  obtain ⟨_, _, tree, _⟩ := expressions sourceContext scope fuel id lowered closed residual signatures declarations generated
  exact tree

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (sameDefinitions : definitions = ambient.definitions)
  (layoutDefinitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (valid : CompatibleExpressionLiterals.ContextValid solved context []) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  (errors : Tree.Errors registry faults (certified matched binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped))
  {mapping : LocationMap} {world : StoreTyping} {canonical actual : Environment} {actualContext : Core.Context}
  {store : Store} {ξ : Renaming} {location : Location} {native : CallableIndexedHistory.NativeFrame}
  (environments : DataHeap.EnvRepresents (storageCatalog values.checked.catalog) mapping world administrative scope environment canonical ambient.definitions)
  (heaps : CompatibleHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type location))
  (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode frame native))
  (unmapped : location ∉ mapping)

include matched binderPolicy allocationPolicy sourceSignatures declarations expressions nativeTyped sameDefinitions layoutDefinitions registered extension valid uninitialized missing faithful observations errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_preserves :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      TypedLexicalWhile.FlowRep (values := values) (registry := registry) functions finalMap finalWorld faults .bool .bool (.returned (.bool true)) value ∧
      CompatibleHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment context after := by
  subst definitions
  exact (certified matched binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped).preserves functions layoutDefinitions registered extension program []
    uninitialized missing faithful observations errors valid unique environments heaps locals agrees typed reference read unmapped (sourceTrace mode)

include matched binderPolicy allocationPolicy sourceSignatures declarations expressions nativeTyped sameDefinitions layoutDefinitions registered extension valid uninitialized missing faithful observations errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_reflects (runtimeViews : FunctionRuntimeViews functions) {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ finalContext outcome sourceHeap finalMap finalWorld,
      TypedScopedStatements.Executes mode program context [] source environment before statements finalContext outcome sourceHeap ∧
      TypedLexicalWhile.FlowRep (values := values) (registry := registry) functions finalMap finalWorld faults .bool .bool outcome value ∧
      CompatibleHeap.HeapRepresents values.checked registry functions finalMap finalWorld sourceHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before sourceHeap ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext sourceHeap := by
  subst definitions
  exact (certified matched binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped).reflects functions layoutDefinitions registered extension program []
    uninitialized missing faithful observations runtimeViews errors valid unique environments heaps locals agrees typed reference read unmapped completed
end CompilerBridge

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Word) }",
    "function nested() returns (Word) { let sum = 0; let m: mapping(Bool => Word); for (let i: Word, i = 0; i < 3; let copy = i, i = copy + 1) { let j = 0; while (j < 2) { j += 1; if (j == 1) { continue; } for (let k = 0; k < 2; k += 1) { m[true] = i * 10 + j + k; sum += k; } } } return m[true] + sum; }",
    "function transfers() returns (Word) { let sum = 0; for (let i = 0; i < 5; let copy = i, i = copy + 1) { if (i == 1) { continue; } { let copy = i; sum += copy; } if (i == 3) { break; } } return sum; }",
    "function early() returns (Word) { for (let i = 0; true; let copy = i, i = copy + 1) { for (let j = 0; j < 2; j += 1) { if (i == 2) { return i + j; } } } return 99; }",
    "function falseFirst() returns (Word) { let i = 17; for (let i = 3; false; let never = 99) { return 0; } return i; }",
    "function bodyFault() returns (Word) { let m: mapping(Bool => Word); let keys: mapping(Bool => Bool); let lazy: mapping(Bool => Word); let missing: Word; for (let i = 0; i < 2; let never = 99) { i += 1; m[keys[true]] = lazy[false] + missing; } return 0; }",
    "function postFault() returns (Word) { let missing: Word; let seen: mapping(Bool => Word); for (let i = 0; true; let copy = i, i = seen[false] + missing, let never = 99) { continue; } return 1; }",
    "function initializerFault() returns (Word) { let missing: Word; let seen: mapping(Bool => Word); for (let ready = 1, let dead = seen[false] + missing; true; ) { return 0; } return 1; }",
    "function conditionFault() returns (Word) { let missing: Bool; let seen: mapping(Bool => Bool); for (let ready = 1; seen[false] || missing; let never = 99) { return 0; } return 1; }"
  ]}] }
private def escape : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function main() returns (Word) { for (let i = 0; false; let copy = i) { } return copy; }"}] }
private def failureResume (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let complete ← entry.invoke []
  let token ← match complete.outcome with
    | .failed token _ => pure token
    | _ => throw (IO.userError "for fixture unexpectedly succeeded")
  SourceCompilerFeatureSupport.require (← complete.diagnostic token).isSome "for failure lost its diagnostic"
  for fuel in [0, 10, 35, 100] do
    let started ← SourceCompilerFeatureSupport.get "for suspension"
      (← complete.initial.run complete.key [] {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed, complete.outcome with
    | .failed actual heap, .failed expected initial =>
        SourceCompilerFeatureSupport.require (actual == expected && heap.heapSize == initial.heapSize)
          "for resume changed failure or executed unreachable allocation"
    | _, _ => throw (IO.userError "for resume changed outcome")

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "imperative for checker" (checkProgram workspace)
  for (name, result) in [("nested", 26), ("transfers", 5), ("early", 2), ("falseFirst", 17)] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    let expected := SourceCompilerFeatureSupport.scalar result
    SourceCompilerFeatureSupport.require ((← entry.run []) == expected) s!"{name}: mixed for/while result changed"
    entry.checkResume [] expected
  let transfers ← SourceCompilerFeatureSupport.compileNamed checked "transfers"
  transfers.checkCells [] [(.word, some (SourceCompilerFeatureSupport.scalar 5)), (.word, some (SourceCompilerFeatureSupport.scalar 3)),
    (.word, some (SourceCompilerFeatureSupport.scalar 0)), (.word, some (SourceCompilerFeatureSupport.scalar 0)),
    (.word, some (SourceCompilerFeatureSupport.scalar 1)), (.word, some (SourceCompilerFeatureSupport.scalar 2)),
    (.word, some (SourceCompilerFeatureSupport.scalar 2)), (.word, some (SourceCompilerFeatureSupport.scalar 3))]
  let falseFirst ← SourceCompilerFeatureSupport.compileNamed checked "falseFirst"
  falseFirst.checkCells [] [(.word, some (SourceCompilerFeatureSupport.scalar 17)), (.word, some (SourceCompilerFeatureSupport.scalar 3))]
  let body ← SourceCompilerFeatureSupport.compileNamed checked "bodyFault"
  failureResume body
  body.checkCells [] [(.mapping .bool .word, none), (.mapping .bool .bool, some (.mapping .bool .bool [])),
    (.mapping .bool .word, some (.mapping .bool .word [])), (.word, none), (.word, some (SourceCompilerFeatureSupport.scalar 1))]
  let post ← SourceCompilerFeatureSupport.compileNamed checked "postFault"
  failureResume post
  post.checkCells [] [(.word, none), (.mapping .bool .word, some (.mapping .bool .word [])),
    (.word, some (SourceCompilerFeatureSupport.scalar 0)), (.word, some (SourceCompilerFeatureSupport.scalar 0))]
  let initializer ← SourceCompilerFeatureSupport.compileNamed checked "initializerFault"
  failureResume initializer
  initializer.checkCells [] [(.word, none), (.mapping .bool .word, some (.mapping .bool .word [])),
    (.word, some (SourceCompilerFeatureSupport.scalar 1))]
  let condition ← SourceCompilerFeatureSupport.compileNamed checked "conditionFault"
  failureResume condition
  condition.checkCells [] [(.bool, none), (.mapping .bool .bool, some (.mapping .bool .bool [])),
    (.word, some (SourceCompilerFeatureSupport.scalar 1))]
  SourceCompilerFeatureSupport.require (match checkProgram escape with | .error _ => true | .ok _ => false) "for post local escaped its scope"
  IO.println "typed imperative for: actual compiler certificates, mixed/nested loops, scoped headers/post, transfer/fault effects and resume GREEN"
end Tests.SourceCoreTypedImperativeFor
end

section
-- leanmerge: from Solcore.Test.SourceCoreTypedImperativeForUnary
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Bare unary assignments preserve source order at every recursive loop
position. Actual code receipts and an independent two-write source trace close
the theorem consumers; runtime fixtures also cover missing operands and resume. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreTypedImperativeForUnary
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedImperativeFor GeneralHeap CompatiblePayload CompatibleEquality ReadOnly
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"unary_for", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "unary_for.solc"⟩, 0, 1⟩
private def expression : ExpressionId := ⟨⟨owner, 0⟩⟩
private def statement (n : Nat) : StatementId := ⟨⟨owner, n + 1⟩⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "x", .mono .word, [], false, none⟩
private def assignment : AssignmentResolution := ⟨⟨binder.id, [], .word⟩, []⟩
private def literal : ExpressionNode := { id := expression, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def assigned : StatementNode := ⟨statement 0, span, .unit, .assignBitNot assignment⟩
private def returned : StatementNode := ⟨statement 1, span, .bool, .returnStmt (some expression)⟩
private def breakNode : StatementNode := ⟨statement 2, span, .unit, .breakStmt⟩
private def loopNode : StatementNode := ⟨statement 3, span, .unit, .forLoop [.assignBitNot assignment] expression [.assignBitNot assignment] [statement 0, statement 2]⟩
private def statements := [statement 3, statement 1]
private def source : TypedSource := {
  owner := owner
  inputs := [binder]
  roots := statements.map .statement
  nodes := [.expression literal, .statement assigned, .statement returned, .statement breakNode, .statement loopNode]
}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def environment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def before : Dynamic.Heap := ⟨[{type := .word, value := some (.word Word.zero)}]⟩
private def middle : Dynamic.Heap := ⟨[{type := .word, value := some (.word Word.zero.bitNot)}]⟩
private def after : Dynamic.Heap := ⟨[{type := .word, value := some (.word Word.zero.bitNot.bitNot)}]⟩
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem booleanTyped : ExpressionHasType source context expression .bool := by
  have admissible : TypeAdmissible context .bool := .bool (by
    simp [TypeParameterBindersWellFormed, context, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal])
  apply ExpressionHasType.ofOrdinary (node := literal) (rawType := .bool) (lookupExpression?_sound rfl)
    (.reference (.builtinBoolean true)) admissible admissible
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem writable : WritableLocal context binder.id .word := by
  apply WritableLocal.withLocal_mono_admissible
  exact .word (by simp [TypeParameterBindersWellFormed, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal])
private theorem rootWritable : ∀ actual, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok actual →
    WritableLocal context assignment.target.root actual.scheme.body := by
  intro actual found
  have : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder := rfl
  cases Except.ok.inj (this.symm.trans found)
  exact writable
private theorem booleanSyntax : CompatibleExpressionTyped.Syntax source expression :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := literal) rfl (.bool _ _)))))))
private theorem syntaxTree (mode : Bool) : TypedImperativeFor.UnarySyntax source context (.statements mode statements) .bool := by
  apply TypedImperativeFor.UnarySyntax.forLoop (node := loopNode) rfl rfl rfl
  · apply TypedImperativeFor.UnarySyntax.initializerBitNot rootWritable rfl (.inl rfl)
    apply TypedImperativeFor.UnarySyntax.initializersDone (conditionNode := literal) rfl rfl booleanTyped booleanSyntax
    · exact .bitNot (node := assigned) rfl rfl rootWritable rfl (.inl rfl) (.breaking (node := breakNode) rfl rfl)
    · exact .bitNot rootWritable rfl (.inl rfl) .nil
  · exact .body (.body (.returnValue [] rfl rfl rfl rfl rfl booleanTyped booleanSyntax))

private theorem sourceFlipped (value : Word) : Dynamic.SourcePlaceSnapshotUpdate program context [] source Dynamic.BitNotSnapshot
    environment ⟨[{type := .word, value := some (.word value)}]⟩ assignment.target (.word value.bitNot)
      ⟨[{type := .word, value := some (.word value.bitNot)}]⟩ := by
  have read : Dynamic.Heap.Reads ⟨[{type := .word, value := some (.word value)}]⟩ ⟨0⟩
      {type := .word, value := some (.word value)} := .intro .head
  refine .intro (selectedHeap := ⟨[{type := .word, value := some (.word value)}]⟩) (target := ⟨⟨0⟩, .word, .word, [], some (.word value)⟩) ?_ ?_
  · exact Dynamic.SourcePlaceResolves.intro (place := assignment.target) (environment := environment) .head read .nil read .initialized .nil
  · exact .intro read rfl .initialized (.leaf (.word value)) (.intro read .head)

private theorem sourceTrace (mode : Bool) : TypedScopedStatements.Executes mode program context [] source environment before
    statements context (.returned (.bool true)) after := by
  have assignedTrace : Dynamic.StatementExecutes program context [] source environment middle (statement 0) context (.fallthrough environment) after :=
    .assignBitNot (lookupStatement?_sound rfl) rfl (sourceFlipped Word.zero.bitNot)
  have loopTrace : Dynamic.StatementExecutes program context [] source environment before (statement 3) context (.fallthrough environment) after := by
    apply Dynamic.StatementExecutes.forLoop (outcome := .fallthrough environment) (lookupStatement?_sound (node := loopNode) rfl) rfl
      (.cons (.assignBitNot (sourceFlipped Word.zero)) .nil)
    apply Dynamic.ForLoopExecutes.breaks
    · exact .intro (node := literal) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil
    · exact .cons assignedTrace (.terminal (.breakStmt (lookupStatement?_sound (node := breakNode) rfl) rfl) (.breaking environment))
  have last : Dynamic.StatementExecutes program context [] source environment after (statement 1) context (.returned (.bool true)) after :=
    .returnValue (lookupStatement?_sound rfl) rfl (.intro (node := literal) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil)
  exact TypedScopedStatements.prepend (lookupStatement?_sound (show source.lookupStatement? (statement 3) = some loopNode from rfl))
    (by intro _ _ _ impossible; cases impossible) loopTrace
    (TypedLexicalControl.terminal_outcome program [] (show source.lookupStatement? (statement 1) = some returned from rfl)
      (by intro expression impossible; cases impossible) (.control last) (.returned _))

section CompilerBridge
variable {layouts : SourceCoreAllocationLayouts.Prepared} {specialization : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {definitions : DataEnvironment}
  {policy : SourceCoreLoops.Policy}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingReason : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  (matched : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingReason)
  (unary : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingReason)
  (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
  (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt specialization active onError)))
  (sourceSignatures : context.signatures = values.checked.signatures)
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  (expressions : ∀ sourceContext scope fuel id lowered,
    sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
    sourceContext.signatures = values.checked.signatures →
    CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
    policy.lowerExpression fuel source scope id reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? id = some node ∧ CompatibleExpressionTyped.Tree readFuel values source sourceContext solved reasonAt scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
  {mode : Bool} {fuel : Nat} {selfReason : Word} {code : Expr} {nativeType : Ty}
  (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements .bool reasonAt mode selfReason = .ok code)
  (nativeTyped : infer? (SourceCoreLocalCell.coreContext scope ++ administrative) code definitions = some nativeType)

include matched unary binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped in
/-- A single whole-code checker receipt supplies both loop typing and the
assignment continuation. The remaining premises are static source certificates. -/
theorem certified : Tree layouts specialization active frame globals onError readFuel values source solved reasonAt definitions administrative
    context scope (.statements mode statements) .bool .bool code := by
  apply tree_of_typed_flow_withBitNot matched.read binderPolicy allocationPolicy ?_ matched unary unique expressions
    (syntaxTree mode) rfl rfl sourceSignatures declarations (by rfl) accepted (infer_sound nativeTyped)
  intro sourceContext closed residual signatures scope fuel id node lowered declarations syntaxValue found typed generated
  obtain ⟨_, _, tree, _⟩ := expressions sourceContext scope fuel id lowered closed residual signatures declarations generated
  exact tree

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (sameDefinitions : definitions = ambient.definitions)
  (layoutDefinitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (valid : CompatibleExpressionLiterals.ContextValid solved context []) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  (errors : Tree.Errors registry faults (certified matched unary binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped))
  {mapping : LocationMap} {world : StoreTyping} {canonical actual : Environment} {actualContext : Core.Context}
  {store : Store} {ξ : Renaming} {location : Location} {native : CallableIndexedHistory.NativeFrame}
  (environments : DataHeap.EnvRepresents (storageCatalog values.checked.catalog) mapping world administrative scope environment canonical ambient.definitions)
  (heaps : CompatibleHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type location))
  (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode frame native))
  (unmapped : location ∉ mapping)

include matched unary binderPolicy allocationPolicy sourceSignatures declarations expressions nativeTyped sameDefinitions layoutDefinitions registered extension valid uninitialized missing faithful observations errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_preserves :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      TypedLexicalWhile.FlowRep (values := values) (registry := registry) functions finalMap finalWorld faults .bool .bool (.returned (.bool true)) value ∧
      CompatibleHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment context after := by
  subst definitions
  exact (certified matched unary binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped).preserves functions layoutDefinitions registered extension program []
    uninitialized missing faithful observations errors valid unique environments heaps locals agrees typed reference read unmapped (sourceTrace mode)

include matched unary binderPolicy allocationPolicy sourceSignatures declarations expressions nativeTyped sameDefinitions layoutDefinitions registered extension valid uninitialized missing faithful observations errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_reflects (runtimeViews : FunctionRuntimeViews functions) {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ finalContext outcome sourceHeap finalMap finalWorld,
      TypedScopedStatements.Executes mode program context [] source environment before statements finalContext outcome sourceHeap ∧
      TypedLexicalWhile.FlowRep (values := values) (registry := registry) functions finalMap finalWorld faults .bool .bool outcome value ∧
      CompatibleHeap.HeapRepresents values.checked registry functions finalMap finalWorld sourceHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before sourceHeap ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext sourceHeap := by
  subst definitions
  exact (certified matched unary binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped).reflects functions layoutDefinitions registered extension program []
    uninitialized missing faithful observations runtimeViews errors valid unique environments heaps locals agrees typed reference read unmapped completed
end CompilerBridge

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function nested() returns (Word) { let x = 7; for (x ~=, let i = 0; i < 2; x ~=, i += 1) { { x ~=; } let j = 0; while (j < 2) { x ~=; j += 1; } } return x; }",
    "function transfer() returns (Word) { let x = 5; for (x ~=, let i = 0; true; x ~=, i += 1) { if (i == 0) { continue; } { x ~=; break; } } return x; }",
    "function early() returns (Word) { let x = 9; for (x ~=; true; x ~=) { x ~=; return x; } return 0; }",
    "function falseFirst() returns (Word) { let x = 2; for (x ~=; false; x ~=) { x ~=; } return x; }",
    "function postFault() returns (Word) { let missing: Word; let seen = 0; for (let i = 0; true; let copy = i, seen = 8, missing ~=, let never = 99) { seen = 3; continue; } return 1; }",
    "function initializerFault() returns (Word) { let missing: Word; let seen = 0; for (seen = 6, missing ~=, let never = 99; true; ) { seen = 3; } return 1; }",
    "function bodyFault() returns (Word) { let missing: Word; let seen = 0; for (seen = 6; true; seen = 7) { { missing ~=; } seen = 8; } return 1; }"
  ]}] }
private def rejected : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function rejected(value: integer) returns (integer) { for (value ~=; false; ) { } return value; }"}] }
private def failureResume (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let complete ← entry.invoke []
  let token ← match complete.outcome with
    | .failed token _ => pure token
    | _ => throw (IO.userError "for fixture unexpectedly succeeded")
  SourceCompilerFeatureSupport.require (← complete.diagnostic token).isSome "for failure lost its diagnostic"
  for fuel in [0, 10, 35, 100] do
    let started ← SourceCompilerFeatureSupport.get "for suspension"
      (← complete.initial.run complete.key [] {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed, complete.outcome with
    | .failed actual heap, .failed expected initial =>
        SourceCompilerFeatureSupport.require (actual == expected && heap.heapSize == initial.heapSize)
          "for resume changed failure or executed unreachable allocation"
    | _, _ => throw (IO.userError "for resume changed outcome")

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "unary for checker" (checkProgram workspace)
  for (name, value) in [("nested", (Word.ofNatModulo 7).bitNot), ("transfer", (Word.ofNatModulo 5).bitNot),
      ("early", Word.ofNatModulo 9), ("falseFirst", (Word.ofNatModulo 2).bitNot)] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    let expected : SourceCorePublicValues.Value := .word value
    SourceCompilerFeatureSupport.require ((← entry.run []) == expected) s!"{name}: unary loop ordering changed"
    entry.checkResume [] expected
  for (name, seen) in [("initializerFault", 6), ("bodyFault", 6)] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    failureResume entry
    entry.checkCells [] [(.word, none), (.word, some (SourceCompilerFeatureSupport.scalar seen))]
  let post ← SourceCompilerFeatureSupport.compileNamed checked "postFault"
  failureResume post
  post.checkCells [] [(.word, none), (.word, some (SourceCompilerFeatureSupport.scalar 8)),
    (.word, some (SourceCompilerFeatureSupport.scalar 0)), (.word, some (SourceCompilerFeatureSupport.scalar 0))]
  SourceCompilerFeatureSupport.require (match checkProgram rejected with | .error _ => true | .ok _ => false)
    "Integer unary compound source admission changed"
  IO.println "typed imperative unary: actual certificates/source trace, every for position, nested effects/faults/resume GREEN"
end Tests.SourceCoreTypedImperativeForUnary
end

section
-- leanmerge: from Solcore.Test.SourceCoreTypedLexicalControl
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! A scoped block lazily initializes a mapping and allocates three locals before
an initializer fails. The fault restores the outer context but preserves every
preceding heap effect; actual checked programs cover nested branch bindings. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreTypedLexicalControl
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedLexicalControl TypedScopedStatements CompatiblePayload GeneralHeap ReadOnly CallableIndexedHistory
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"typed_mixed_binding", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "typed_mixed.solc"⟩, 0, 1⟩
private def expression (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def binder (index : Nat) : TypedBinder := ⟨⟨owner, index⟩, "value", .mono .bool, [], false, none⟩
private def mappingType : TypeSystem.Ty := .mapping .bool .bool
private def inputBinder : TypedBinder := ⟨⟨owner, 0⟩, "input", .mono mappingType, [], false, none⟩
private def inputNode : ExpressionNode := {id := expression 0, span, type := mappingType, form := .reference "input" (.local inputBinder.id)}
private def keyNode : ExpressionNode := {id := expression 2, span, type := .bool, form := .reference "true" (.builtinBoolean true)}
private def indexNode : ExpressionNode := {id := expression 3, span, type := .bool, form := .index (expression 0) (expression 2)}
private def missingNode : ExpressionNode := {id := expression 1, span, type := .bool, form := .reference "missing" (.local (binder 2).id)}
private def first : StatementNode := ⟨statement 0, span, .unit, .letDecl (binder 1) (some (expression 3))⟩
private def second : StatementNode := ⟨statement 1, span, .unit, .letDecl (binder 2) none⟩
private def third : StatementNode := ⟨statement 2, span, .unit, .letDecl (binder 3) (some (expression 3))⟩
private def fourth : StatementNode := ⟨statement 3, span, .unit, .letDecl (binder 4) (some (expression 1))⟩
private def returned : StatementNode := ⟨statement 4, span, .unit, .returnStmt none⟩
private def innerStatements := [statement 0, statement 1, statement 2, statement 3, statement 4]
private def scopedBlock : StatementNode := ⟨statement 5, span, .unit, .block innerStatements⟩
private def statements := [statement 5]
private def source : TypedSource := {
  owner, inputs := [inputBinder], roots := statements.map .statement,
  nodes := [.expression inputNode, .expression missingNode, .expression keyNode, .expression indexNode, .statement first, .statement second,
    .statement third, .statement fourth, .statement returned, .statement scopedBlock] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def initial : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal inputBinder.id inputBinder.scheme
private def context1 := initial.withLocal (binder 1).id (binder 1).scheme
private def context2 := context1.withLocal (binder 2).id (binder 2).scheme
private def context3 := context2.withLocal (binder 3).id (binder 3).scheme
private def context4 := context3.withLocal (binder 4).id (binder 4).scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def reason := Word.ofNatModulo 37
private theorem extend {context : SourceSemantics.Context} (index : Nat)
    (binders : TypeParameterBindersWellFormed context) (fresh : LocalFresh context (binder index).id) :
    BinderExtends owner context (binder index) (context.withLocal (binder index).id (binder index).scheme) := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {binders, quantified_nodup := by simp [binder, TypeSystem.Scheme.mono], body := .builtin .bool}
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl }
  · exact fresh
private theorem extension1 : BinderExtends owner initial (binder 1) context1 := by
  apply extend 1
  · simp [TypeParameterBindersWellFormed, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, signatures]
  · simp [LocalFresh, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder, inputBinder]
private theorem extension2 : BinderExtends owner context1 (binder 2) context2 := by
  apply extend 2
  · simp [TypeParameterBindersWellFormed, context1, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, signatures]
  · simp [LocalFresh, context1, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder, inputBinder]
private theorem extension3 : BinderExtends owner context2 (binder 3) context3 := by
  apply extend 3
  · simp [TypeParameterBindersWellFormed, context1, context2, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, signatures]
  · simp [LocalFresh, context1, context2, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder, inputBinder]
private theorem extension4 : BinderExtends owner context3 (binder 4) context4 := by
  apply extend 4
  · simp [TypeParameterBindersWellFormed, context1, context2, context3, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, signatures]
  · simp [LocalFresh, context1, context2, context3, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder, inputBinder]
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem localTyped {context : SourceSemantics.Context} {node : ExpressionNode} {index : Nat}
    (found : source.lookupExpression? node.id = some node)
    (form : node.form = .reference "input" (.local (binder index).id) ∨ node.form = .reference "missing" (.local (binder index).id))
    (type : node.type = .bool) (requirements : node.requirements = []) (coercions : node.coercions = [])
    (binders : TypeParameterBindersWellFormed context)
    (lookup : Resolved.LocalScope.Lookup context.locals (binder index).id (binder index).scheme)
    (schemes : context.LocalSchemeRequirementsLookup (binder index).id []) :
    ExpressionHasType source context node.id node.type := by
  have admitted : TypeAdmissible context .bool := .bool binders
  rcases form with form | form
  all_goals
    apply ExpressionHasType.ofOrdinary (rawType := .bool) (owned := []) (lookupExpression?_sound found)
    · rw [form]
      exact .reference (.local lookup schemes (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible admitted) []
        .empty (by intro metavariable replacement member; cases member) (SchemeInstantiates.empty_apply _)
        (by simp) (by intro _ member; cases member) .nil))
    · exact admitted
    · exact type ▸ admitted
    · intro requirement member; cases member
    · rw [coercions, type]; exact .nil _
    · simp [requirements, coercions, coercionRequirementIds]
private theorem inputTyped {context : SourceSemantics.Context}
    (binders : TypeParameterBindersWellFormed context)
    (lookup : Resolved.LocalScope.Lookup context.locals inputBinder.id inputBinder.scheme)
    (schemes : context.LocalSchemeRequirementsLookup inputBinder.id []) :
    ExpressionHasType source context (expression 0) mappingType := by
  have admitted : TypeAdmissible context mappingType := .mapping (.bool binders) (.bool binders)
  apply ExpressionHasType.ofOrdinary (node := inputNode) (rawType := mappingType) (lookupExpression?_sound rfl)
    (.reference (.local lookup schemes (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible admitted) []
      .empty (by intro metavariable replacement member; cases member) (SchemeInstantiates.empty_apply _)
      (by simp) (by intro _ member; cases member) .nil))) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexTyped {context : SourceSemantics.Context}
    (binders : TypeParameterBindersWellFormed context)
    (lookup : Resolved.LocalScope.Lookup context.locals inputBinder.id inputBinder.scheme)
    (schemes : context.LocalSchemeRequirementsLookup inputBinder.id []) :
    ExpressionHasType source context (expression 3) .bool := by
  have admitted : TypeAdmissible context .bool := .bool binders
  have key : ExpressionHasType source context (expression 2) .bool := by
    apply ExpressionHasType.ofOrdinary (node := keyNode) (rawType := .bool) (lookupExpression?_sound rfl)
      (.reference (.builtinBoolean true)) admitted admitted
    · intro requirement member; cases member
    · exact .nil _
    · rfl
  apply ExpressionHasType.ofOrdinary (node := indexNode) (rawType := .bool) (lookupExpression?_sound rfl)
    (.index (inputTyped binders lookup schemes) key) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem inputInitial : ExpressionHasType source initial (expression 3) .bool :=
  indexTyped ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _) .head .head
private theorem inputSecond : ExpressionHasType source context2 (expression 3) .bool :=
  indexTyped ((((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _).withLocal _ _).withLocal _ _)
    (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
private theorem missingThird : ExpressionHasType source context3 (expression 1) .bool := by
  apply localTyped (node := missingNode) (index := 2) rfl (.inr rfl) rfl rfl rfl
  · exact ((((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _).withLocal _ _).withLocal _ _).withLocal _ _
  · exact .tail (by decide) .head
  · exact .tail (by decide) .head
private theorem inputSyntax : CompatibleExpressionTyped.Syntax source (expression 3) :=
  .index (node := indexNode) (keyNode := keyNode) rfl rfl rfl .bool
    (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.read (node := inputNode) rfl rfl)))))))
    (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := keyNode) rfl (.bool _ _))))))))
private theorem missingSyntax : CompatibleExpressionTyped.Syntax source (expression 1) :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.read (node := missingNode) rfl rfl))))))
private theorem innerSyntax : TypedLexicalControl.Syntax source initial false innerStatements .unit :=
  .initialized (node := first) (initializerNode := indexNode) rfl rfl rfl rfl extension1 (by decide)
    rfl rfl inputInitial inputSyntax
    (.uninitialized (node := second) rfl rfl rfl rfl extension2 (by decide)
      (.initialized (node := third) (initializerNode := indexNode) rfl rfl rfl rfl extension3 (by decide)
        rfl rfl inputSecond inputSyntax
        (.initialized (node := fourth) (initializerNode := missingNode) rfl rfl rfl rfl extension4 (by decide)
          rfl rfl missingThird missingSyntax (.body (.returnUnit (node := returned) [] rfl rfl rfl)))))
private theorem syntaxTree (mode : Bool) : TypedLexicalControl.Syntax source initial mode statements .unit :=
  .block (node := scopedBlock) rfl rfl rfl innerSyntax (.body (.nil (.inr rfl)))
private theorem valid : CompatibleExpressionLiterals.ContextValid [] initial [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal]
  · intro requirement member
    simp [initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member
      simp [initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
private theorem prepared : (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType, .bool, .unit]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType, .bool, .unit]).toOption.get prepared
private def values := SourceCoreCompatibleValues.Context.initial checked
private theorem nativeExists : (checked.catalog.project mappingType).toOption.isSome = true := by cbv
private def nativeType := (checked.catalog.project mappingType).toOption.get nativeExists
private def scope : SourceCoreLocalCell.Scope := [(inputBinder.id, nativeType)]
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def expressionPolicy := SourceCoreCompatibleDataExpressions.functionPolicy 10 values
private def onError (_ : SourceCoreAllocationLayouts.Error) : SourceCoreBasic.Error := .traversalExhausted (.declaration owner)
private def policy (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) : SourceCoreLoops.Policy := {
  lowerExpression := fun fuel source scope id reasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody fuel compilation source scope id reasonAt
  readStatement := SourceCoreCompatibleDataExpressions.readStatement checked
  lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder checked
  sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt ⟨owner, []⟩ [] onError)) }
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source scope initial := by
  intro id declared index type selected authentic
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst id
    have found : SourceCoreDataPlaces.rootBinder source inputBinder.id = .ok inputBinder := rfl
    rw [found] at authentic; cases authentic
    exact .head
  · simp at selected
private theorem metadata {id : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp [source] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

private theorem certified {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {mode : Bool} {code : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) fuel source scope
      statements .unit (fun _ => reason) mode reason = .ok code) :
    TypedLexicalControl.Tree layouts ⟨owner, []⟩ [] frame globals onError 10 values source [] (fun _ => reason)
      initial scope mode statements .unit .unit code := by
  apply tree_of_flow rfl (fun _ _ _ => rfl) rfl ?_ (syntaxTree mode) rfl rfl rfl declarations rfl accepted
  intro current closed residual sameSignatures currentScope budget id node lowered declared childSyntax found typed generated
  exact CompatibleExpressionTyped.tree_of_functions unique declared sameSignatures closed residual
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ (fun _ _ _ found => metadata found)
    childSyntax found typed generated

private def sourceEnvironment : Dynamic.Environment := [(inputBinder.id, ⟨0⟩)]
private def environment1 : Dynamic.Environment := ((binder 1).id, ⟨1⟩) :: sourceEnvironment
private def environment2 : Dynamic.Environment := ((binder 2).id, ⟨2⟩) :: environment1
private def environment3 : Dynamic.Environment := ((binder 3).id, ⟨3⟩) :: environment2
private def sourceHeap : Dynamic.Heap := ⟨[⟨mappingType, none, none⟩]⟩
private def initializedHeap : Dynamic.Heap := ⟨[⟨mappingType, some (.mapping .bool .bool []), none⟩]⟩
private def heap1 : Dynamic.Heap := ⟨initializedHeap.cells ++ [⟨.bool, some (.bool false), none⟩]⟩
private def heap2 : Dynamic.Heap := ⟨heap1.cells ++ [⟨.bool, none, none⟩]⟩
private def heap3 : Dynamic.Heap := ⟨heap2.cells ++ [⟨.bool, some (.bool false), none⟩]⟩
private theorem firstIndex : Dynamic.ExpressionEvaluates program initial [] source sourceEnvironment sourceHeap
    (expression 3) (.bool false) initializedHeap := by
  apply Dynamic.ExpressionEvaluates.intro (node := indexNode) (raw := .bool false) (middle := initializedHeap) (lookupExpression?_sound rfl)
  · apply Dynamic.ExpressionFormEvaluates.indexDefault (coercions := []) rfl
    · exact .intro (node := inputNode) (lookupExpression?_sound rfl)
        (.localEmptyMapping rfl .head (.intro .head) rfl rfl rfl (.intro (.intro .head) .head)) .nil
    · exact .intro (node := keyNode) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil
    · exact .nil
    · exact .bool
  · exact .nil
private theorem thirdIndex : Dynamic.ExpressionEvaluates program context2 [] source environment2 heap2
    (expression 3) (.bool false) heap2 := by
  apply Dynamic.ExpressionEvaluates.intro (node := indexNode) (raw := .bool false) (middle := heap2) (lookupExpression?_sound rfl)
  · apply Dynamic.ExpressionFormEvaluates.indexDefault (coercions := []) rfl
    · exact .intro (node := inputNode) (lookupExpression?_sound rfl)
        (.local rfl (.tail (by decide) (.tail (by decide) .head)) (.intro .head) rfl rfl) .nil
    · exact .intro (node := keyNode) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil
    · exact .nil
    · exact .bool
  · exact .nil
private theorem innerFailure : Dynamic.StatementsFault program initial [] source sourceEnvironment sourceHeap
    innerStatements context3 (.uninitializedLocation ⟨2⟩) heap3 := by
  apply Dynamic.StatementsFault.tail
    (Dynamic.StatementExecutes.letInitialized (node := first) (lookupStatement?_sound rfl) rfl firstIndex
      rfl extension1 .append)
  apply Dynamic.StatementsFault.tail
    (Dynamic.StatementExecutes.letUninitialized (node := second) (lookupStatement?_sound rfl) rfl rfl extension2 .append)
  apply Dynamic.StatementsFault.tail
    (Dynamic.StatementExecutes.letInitialized (node := third) (lookupStatement?_sound rfl) rfl thirdIndex
      rfl extension3 .append)
  apply Dynamic.StatementsFault.head
  apply Dynamic.StatementFaults.letInitializer (node := fourth) (lookupStatement?_sound rfl) rfl rfl
  apply Dynamic.ExpressionFaults.form (node := missingNode) (lookupExpression?_sound rfl)
  exact .localUninitialized (owned := []) (coercions := []) (cell := ⟨.bool, none, none⟩)
    rfl (.tail (by decide) .head) (.intro (.tail (.tail .head))) rfl rfl
      (by rintro ⟨key, value, impossible⟩; cases impossible)

private theorem sourceFailure (mode : Bool) : Executes mode program initial [] source sourceEnvironment sourceHeap
    statements initial (.fault (.uninitializedLocation ⟨2⟩)) heap3 := by
  exact TypedScopedStatements.head_fault mode [] (.block (lookupStatement?_sound (node := scopedBlock) rfl) rfl innerFailure)

private def faults : FunctionCalls.FaultRep := fun error token =>
  ((∃ location, error = .uninitializedLocation location) ∧ token = reason) ∨
  (∃ key value tag, MetadataRep values.registry (.mapping key value) tag ∧ error = .missingMappingDefault value ∧ token = reason.add tag)
private theorem uninitialized : ∀ (id : ExpressionId) location, faults (.uninitializedLocation location) ((fun _ => reason) id) :=
  fun _ location => .inl ⟨⟨location, rfl⟩, rfl⟩
private theorem missing : ∀ (id : ExpressionId) key value tag, MetadataRep values.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) (((fun _ => reason) id).add tag) :=
  fun _ key value tag owned => .inr ⟨key, value, tag, owned, rfl, rfl⟩

private theorem failureContext_ne_full : context3 ≠ context4 := by
  intro same
  have impossible : 4 = 5 := congrArg (fun context => context.locals.length) same
  omega

/-- Actual completed scoped flow reconstructs its independent source trace
and result-dependent lexical environment. -/
theorem compiled_reflects {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {mode : Bool} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) fuel source scope
      statements .unit (fun _ => reason) mode reason = .ok code)
    {mapping world administrative actualContext canonical actual heap store ξ contextLocation native value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap initial.locals sourceEnvironment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      Executes mode program initial [] source sourceEnvironment heap
        statements resultContext outcome after ∧
      TypedScopedStatements.FlowRep (values := values) (registry := values.registry) functions finalMap finalWorld
        faults .unit .unit outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      LexicalResult checked ambient.definitions finalMap finalWorld administrative source.owner
        initial scope sourceEnvironment resultContext after := by
  have tree := certified accepted
  exact TypedLexicalControl.Tree.reflects (values := values) (ambient := ambient) (faults := faults)
    functions definitions registered (.refl _) program [] uninitialized missing
    tree valid environments heaps locals agrees typed reference read unmapped completed

theorem compiled_failure_preserves {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {mode : Bool} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) fuel source scope
      statements .unit (fun _ => reason) mode reason = .ok code)
    {mapping world administrative actualContext canonical actual store ξ contextLocation native}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world sourceHeap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      TypedScopedStatements.FlowRep (values := values) (registry := values.registry) functions finalMap finalWorld
        faults .unit .unit (.fault (.uninitializedLocation ⟨2⟩)) value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld heap3 finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend sourceHeap heap3 ∧
      LexicalResult checked ambient.definitions finalMap finalWorld administrative source.owner
        initial scope sourceEnvironment initial heap3 := by
  have tree := certified accepted
  exact TypedLexicalControl.Tree.preserves (values := values) (ambient := ambient) (faults := faults)
    functions definitions registered (.refl _) program [] uninitialized missing
    tree valid unique environments heaps (.cons (.intro .head) rfl (.ordinary rfl rfl) .nil)
    agrees typed reference read unmapped (sourceFailure mode)

private def rawWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Bool) }",
    "function nested(take: Bool) returns (Bool) { let x = true; let m: mapping(Bool => Bool); if (take) { let x = m[true]; { let y = !x; y; } } else { let x = !m[false]; { let y: Bool; x; } } let out = x; return out; }",
    "function shadow() returns (Bool) { let x = true; { let x = false; { let x = true; x; } x; } return x; }",
    "function fail() returns (Bool) { let m: mapping(Bool => Bool); { let a = m[true]; let missing: Bool; if (true) { let b = !m[false]; let failed = (m[true], missing); let never = false; } } return true; }",
    "function missingDefault() returns (Bool) { let m: mapping(Bool => Box); if (false) { let skip = false; } else { let a = true; { let gap: Word; let failed = m[true]; } } return true; }",
    "function early() returns (Bool) { let m: mapping(Bool => Bool); { let x = m[true]; if (!x) { let hidden: Word; return !x; } } let unreachable = false; return false; }",
    "function boxed() returns (Box) { { let unused: Word; } if (true) { let flag = true; return Box(flag); } return Box(false); }"]}] }

private def requireFailureResume (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let invocation ← entry.invoke []
  match invocation.outcome with
  | .failed token complete =>
      SourceCompilerFeatureSupport.require (← invocation.diagnostic token).isSome "lexical initializer fault diagnostic missing"
      let suspended ← SourceCompilerFeatureSupport.get "lexical suspension"
        (← invocation.initial.run invocation.key [] {SourceCompilerFeatureSupport.executionOptions with executionFuel := 13})
      let checkpoint ← match suspended with
        | .outOfFuel checkpoint => pure checkpoint
        | _ => throw (IO.userError "lexical fixture did not suspend")
      match ← checkpoint.resume 300000 1024 with
      | .failed resumed finished =>
          SourceCompilerFeatureSupport.require (resumed == token && finished.heapSize == complete.heapSize)
            "lexical resumption changed failure or allocated an unreachable binding"
      | _ => throw (IO.userError "lexical checkpoint changed outcome")
  | _ => throw (IO.userError "lexical initializer unexpectedly succeeded")

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "typed lexical checker" (checkProgram rawWorkspace)
  let nested ← SourceCompilerFeatureSupport.compileNamed checked "nested"
  for take in [false, true] do
    SourceCompilerFeatureSupport.require ((← nested.run [.bool take]) == .bool true)
      "scoped branch did not restore its outer binding"
    nested.checkCells [.bool take] [(.bool, some (.bool take)), (.bool, some (.bool true)),
      (.mapping .bool .bool, some (.mapping .bool .bool [])), (.bool, some (.bool (!take))),
      (.bool, if take then some (.bool true) else none), (.bool, some (.bool true))]
    nested.checkResume [.bool take] (.bool true)
  let shadow ← SourceCompilerFeatureSupport.compileNamed checked "shadow"
  SourceCompilerFeatureSupport.require ((← shadow.run []) == .bool true) "nested shadowing leaked its scope"
  shadow.checkCells [] [(.bool, some (.bool true)), (.bool, some (.bool false)), (.bool, some (.bool true))]
  shadow.checkResume [] (.bool true)
  let failed ← SourceCompilerFeatureSupport.compileNamed checked "fail"
  requireFailureResume failed
  failed.checkCells [] [(.mapping .bool .bool, some (.mapping .bool .bool [])),
    (.bool, some (.bool false)), (.bool, none), (.bool, some (.bool true))]
  let missingDefault ← SourceCompilerFeatureSupport.compileNamed checked "missingDefault"
  requireFailureResume missingDefault
  let invocation ← missingDefault.invoke []
  match invocation.outcome with
  | .failed token _ =>
      match ← invocation.diagnostic token with
      | some {error := .typeMismatch _ none, span := some _, ..} => pure ()
      | _ => throw (IO.userError "scoped missing-default initializer lost raw metadata/span")
  | _ => throw (IO.userError "scoped missing-default initializer did not fail")
  let cells := (SourceCompilerFeatureSupport.sourceState (← missingDefault.audit [])).heap
  match cells with
  | [mapping, first, gap] =>
      SourceCompilerFeatureSupport.require ((match first.value with | some (.bool true) => true | _ => false) && gap.type == .word && gap.value.isNone)
        "scoped initializer fault changed preceding allocation order"
      match mapping.value with
      | some (.mapping .bool _ []) => pure ()
      | _ => throw (IO.userError "scoped initializer fault lost lazy root initialization")
  | _ => throw (IO.userError "scoped initializer fault allocated a failed or skipped branch binding")
  let early ← SourceCompilerFeatureSupport.compileNamed checked "early"
  SourceCompilerFeatureSupport.require ((← early.run []) == .bool true) "scoped early return was discarded"
  early.checkCells [] [(.mapping .bool .bool, some (.mapping .bool .bool [])), (.bool, some (.bool false)), (.word, none)]
  early.checkResume [] (.bool true)
  let boxed ← SourceCompilerFeatureSupport.compileNamed checked "boxed"
  match ← boxed.run [] with
  | .constructed _ [.bool true] => pure ()
  | _ => throw (IO.userError "typed lexical nominal return changed")
  IO.println "typed lexical control: mixed bindings, scoped restoration, both branches, shadowing, index effects/faults, early return and resume GREEN"
end Tests.SourceCoreTypedLexicalControl
end

section
-- leanmerge: from Solcore.Test.SourceCoreTypedLexicalNamedParameters
#check_failure Solcore.SourceSemantics.CoreLowering.TypedLexicalNamedBody.Certificate.mk
#check_failure Solcore.SourceSemantics.CoreLowering.TypedMixedNamedParameters.Entry.mk
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! A static mixed-body receipt and an independent initializer-fault trace
retain the context before the failed declaration. Checked cached calls retain
ordered parameter/local cells, raw mapping metadata and real Core resumption. -/
set_option autoImplicit false
namespace Tests.SourceCoreTypedLexicalNamedParameters
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedLexicalNamedBody

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"typed_mixed_named", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "mixed_named.solc"⟩, 0, 1⟩
private def expression : ExpressionId := ⟨⟨owner, 0⟩⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def binder (index : Nat) : TypedBinder := ⟨⟨owner, index⟩, "value", .mono .bool, [], false, none⟩
private def absentNode : ExpressionNode := {
  id := expression, span, type := .bool, form := .reference "value" (.local (binder 0).id) }
private def first : StatementNode := ⟨statement 0, span, .unit, .letDecl (binder 0) none⟩
private def second : StatementNode := ⟨statement 1, span, .unit, .letDecl (binder 1) (some expression)⟩
private def returned : StatementNode := ⟨statement 2, span, .unit, .returnStmt none⟩
private def innerStatements := [statement 0, statement 1]
private def scopedBlock : StatementNode := ⟨statement 3, span, .unit, .block innerStatements⟩
private def statements := [statement 3, statement 2]
private def source : TypedSource := {
  owner, inputs := [], roots := statements.map .statement,
  nodes := [.expression absentNode, .statement first, .statement second, .statement returned, .statement scopedBlock] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def initial := SourceSemantics.Context.ofSignatures signatures
private def entered := initial.withLocal (binder 0).id (binder 0).scheme
private def complete := entered.withLocal (binder 1).id (binder 1).scheme
private theorem firstExtension : BinderExtends owner initial (binder 0) entered := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {binders := .ofSignatures signatures, quantified_nodup := by simp [binder, TypeSystem.Scheme.mono], body := .builtin .bool}
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl }
  · simp [LocalFresh, initial, SourceSemantics.Context.ofSignatures]
private theorem secondExtension : BinderExtends owner entered (binder 1) complete := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {binders := (TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _, quantified_nodup := by simp [binder, TypeSystem.Scheme.mono], body := .builtin .bool}
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl }
  · simp [LocalFresh, entered, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder]
private theorem absentTyped : ExpressionHasType source entered expression .bool := by
  have admitted : TypeAdmissible entered .bool := .bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _)
  apply ExpressionHasType.ofOrdinary (node := absentNode) (rawType := .bool) (lookupExpression?_sound rfl)
    (.reference (.local .head .head (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible admitted) []
      .empty (by intro metavariable replacement member; cases member) (SchemeInstantiates.empty_apply _)
      (by simp) (by intro _ member; cases member) .nil))) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem absentSyntax : CompatibleExpressionTyped.Syntax source expression :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.read (node := absentNode) rfl rfl))))))
private theorem innerSyntax : TypedLexicalControl.Syntax source initial false innerStatements .unit :=
  .uninitialized (node := first) rfl rfl rfl rfl firstExtension (by decide)
    (.initialized (node := second) (initializerNode := absentNode) rfl rfl rfl rfl secondExtension (by decide)
      rfl rfl absentTyped absentSyntax (.body (.nil (.inl rfl))))
private theorem syntaxTree : TypedLexicalControl.Syntax source initial true statements .unit :=
  .block (node := scopedBlock) rfl rfl rfl innerSyntax (.body (.returnUnit (node := returned) [] rfl rfl rfl))
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private def compilation (plan : SourceSpecializationWorklist.Plan) : SourceCoreFunctions.Context := {
  plan, owner := ⟨owner, []⟩, globals := [], administrativePrefix := 1, solvedRequirements := [], internalReason := Word.zero }
private def policy (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout)
    (globals : Nat) (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (program : CheckedProgram) (representation : SourceCoreGeneralFunctions.Representation)
    (plan : SourceSpecializationWorklist.Plan) (values : SourceCoreCompatibleValues.Context)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program) : SourceCoreLoops.Policy := {
  lowerExpression := SourceCoreGeneralFunctions.lowerContextualExpression program representation program.signatures
    ⟨[]⟩ [] assignments diagnostics (compilation plan) none none none
  readStatement := SourceCoreCompatibleDataExpressions.readStatement values.checked
  lowerBinder := SourceCoreGeneralFunctions.contextualBinder representation ⟨[]⟩ ⟨owner, []⟩ []
  sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt ⟨owner, []⟩ [] onError)) }

/-- Actual contextual success supplies both let receipts and the remaining
body tree. The static premises contain no child/body semantic theorem. -/
theorem lexical_certificate (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout)
    (globals : Nat) (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (program : CheckedProgram) (representation : SourceCoreGeneralFunctions.Representation)
    (plan : SourceSpecializationWorklist.Plan) (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (sourceSignatures : initial.signatures = values.checked.signatures)
    (readExpression : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (lowerBinder : representation.expressions.lowerBinder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked)
    {fuel : Nat} {code : Expr} (fellThrough escaped : Word)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy
      (policy layouts frame globals onError program representation plan values assignments diagnostics) fuel
      source [] statements .unit (fun _ => Word.zero) fellThrough escaped = .ok code) :
    Nonempty (Certificate layouts ⟨owner, []⟩ [] frame globals onError readFuel values source initial []
      (fun _ => Word.zero) [] statements .unit .unit
      (policy layouts frame globals onError program representation plan values assignments diagnostics) fuel fellThrough escaped code) := by
  apply of_contextual (locals := ⟨[]⟩) (compilation := compilation plan)
      (native := none) (parent := none) (skipInitializer := none) ?_ unique rfl rfl ?_ sourceSignatures
      readExpression lowerRead leafLowerer rfl lowerBinder rfl rfl rfl syntaxTree rfl accepted
  · constructor
    · intro id node _ found
      have member := (lookupExpression?_sound found).1
      simp [source] at member
      subst node
      rfl
    · intro id node _ found
      have member := (lookupExpression?_sound found).1
      simp [source] at member
      subst node
      rfl
    · intros; rfl
    · intros; rfl
  · intro id declared index type selected authentic
    cases selected

private def closure : Dynamic.Closure := ⟨[], .unit, statements, source, [], initial, []⟩
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def faultHeap : Dynamic.Heap := ⟨[⟨.bool, none, none⟩]⟩

/-- A fault inside the block restores its enclosing context while retaining the
uninitialized cell. The failed declaration never enters the source environment. -/
theorem scoped_initializer_fault :
    Dynamic.FunctionStatementsFault program initial [] source [] ⟨[]⟩ statements initial
      (.uninitializedLocation ⟨0⟩) faultHeap ∧
    FunctionCallBody.Trace program closure initial [] ⟨[]⟩ (.fault (.uninitializedLocation ⟨0⟩)) faultHeap ∧
    initial ≠ entered := by
  have inner : Dynamic.StatementsFault program initial [] source [] ⟨[]⟩ innerStatements entered
      (.uninitializedLocation ⟨0⟩) faultHeap := by
    apply Dynamic.StatementsFault.tail
      (Dynamic.StatementExecutes.letUninitialized (node := first) (lookupStatement?_sound rfl) rfl rfl firstExtension .append)
    apply Dynamic.StatementsFault.head
    apply Dynamic.StatementFaults.letInitializer (node := second) (lookupStatement?_sound rfl) rfl rfl
    apply Dynamic.ExpressionFaults.form (node := absentNode) (lookupExpression?_sound rfl)
    exact .localUninitialized (owned := []) (coercions := []) (cell := ⟨.bool, none, none⟩)
      rfl .head (.intro .head) rfl rfl (by rintro ⟨key, value, impossible⟩; cases impossible)
  have failed : Dynamic.FunctionStatementsFault program initial [] source [] ⟨[]⟩ statements initial
      (.uninitializedLocation ⟨0⟩) faultHeap :=
    .head (.block (lookupStatement?_sound rfl) rfl inner)
  refine ⟨failed, .fault failed, ?_⟩
  intro same
  have impossible : 0 = 1 := congrArg (fun context => context.locals.length) same
  omega

/-- Empty scoped branches at a Bool result do not acquire a false Unit fact. -/
theorem scoped_empty_bool :
    TypedLexicalControl.Syntax source initial false [] .bool ∧
    TypedScopedStatements.Executes false program initial [] source [] ⟨[]⟩ [] initial (.fallthrough []) ⟨[]⟩ :=
  ⟨.body (.nil (.inl rfl)), .control .nil⟩

private def unitBlock : StatementNode := ⟨statement 4, span, .unit, .block [statement 0]⟩
private def unitSource : TypedSource := {source with roots := [.statement (statement 4)], nodes := source.nodes ++ [.statement unitBlock]}
private theorem unitSyntax : TypedLexicalControl.Syntax unitSource initial true [statement 4] .unit :=
  .block (node := unitBlock) rfl rfl rfl
    (.uninitialized (node := first) rfl rfl rfl rfl firstExtension (by decide) (.body (.nil (.inl rfl))))
    (.body (.nil (.inr rfl)))
private theorem unitUnique : NodeOccurrencesUnique unitSource := by cbv; decide

/-- The source derivation allocates inside a false-mode block and restores the
outer environment/context. The function-mode Unit fact is derived, not supplied. -/
theorem unit_source_exit :
    Dynamic.FunctionStatementsExecute program initial [] unitSource [] ⟨[]⟩ [statement 4] initial (.fallthrough []) faultHeap ∧
    (let expected := TypeSystem.Ty.unit; expected = .unit) := by
  have executed : Dynamic.FunctionStatementsExecute program initial [] unitSource [] ⟨[]⟩ [statement 4] initial (.fallthrough []) faultHeap :=
    .singleton (lookupStatement?_sound rfl) (by intro expression; simp [unitBlock])
      (.block (node := unitBlock) (lookupStatement?_sound rfl) rfl
        (.cons (.letUninitialized (node := first) (lookupStatement?_sound rfl) rfl rfl firstExtension .append) .nil))
  exact ⟨executed, true_fallthrough_unit unitSyntax unitUnique (.control executed)⟩

private def content : String := String.intercalate "\n" [
  "enum Item { Item(Bool) }",
  "function unit() { let outer: Word; { let inner = true; } }",
  "function nested(flag: Bool, raw: mapping(Bool => Bool)) returns (Bool) { let x = true; let m: mapping(Bool => Bool); if (flag) { let x = m[true]; { let y = !x; y; } } else { let x = !raw[false]; { let gap: Bool; x; } } let out = x; return out; }",
  "function shadow(flag: Bool) returns (Bool) { let x = flag; { let x = !flag; { let x = flag; x; } x; } return x; }",
  "function early(flag: Bool) returns (Bool) { let m: mapping(Bool => Bool); { let x = m[flag]; if (!x) { let hidden: Word; return !x; } } let unreachable = false; return false; }",
  "function conditionFault(flag: Bool) returns (Bool) { let gap: Bool; if (gap) { let skipped = flag; } return flag; }",
  "function branchFault(flag: Bool) returns (Bool) { let outer = flag; { let gap: Bool; if (flag) { let before = !outer; let failed = gap; } else { let skipped = outer; } } return outer; }",
  "function missing(flag: Bool) returns (Bool) { let m: mapping(Bool => Item); if (flag) { let gap: Word; let failed = m[flag]; } return false; }",
  "function identity(flag: Bool) returns (Bool) { return flag; }",
  "function callable(f: function(Bool) returns (Bool), flag: Bool) returns (function(Bool) returns (Bool)) { { let alias = f; alias; } if (flag) { let same = f; return same; } return f; }"
]

private def finished (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initialState : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initialState
  let result ← SourceCoreUnifiedCorpusSupport.get "typed lexical named resume" (SourceCoreUnifiedCompilation.Result.resume first 300000)
  pure result.observation

private def assertCells (initialState final : SourceTypedRuntime.RuntimeState)
    (cells : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (name : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initialState.heap.length) == reprStr initialState.heap)
    s!"typed lexical named prefix changed {name}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initialState.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr cells)
    s!"typed lexical named ordered cells changed {name}: {reprStr final.heap}"

private def check (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (expected : SourceTypedRuntime.Value)
    (cells : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (initialState : SourceTypedRuntime.RuntimeState) : IO Unit := do
  for fuel in [0, 41, 300000] do
    match ← finished compiled name arguments fuel initialState with
    | .done value final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr expected) s!"typed lexical named result changed {name}"
      assertCells initialState final cells name
      SourceCoreUnifiedCorpusSupport.assertTrue (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
        s!"typed lexical named unsafe final heap {name}"
    | other => throw (IO.userError s!"typed lexical named failed {name}: {reprStr other}")

private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name localName : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "typed lexical named fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == localName) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "typed lexical named exact binder missing")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "typed lexical named bodies" content
    ["unit", "nested", "shadow", "early", "conditionFault", "branchFault", "missing", "identity", "callable"]
  let initialState : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩,
    ⟨.word, some (.word (Word.ofNatModulo 731))⟩]}
  let yes : SourceTypedRuntime.Value := .bool true
  let no : SourceTypedRuntime.Value := .bool false
  check compiled "unit" [] .unit [(.word, none), (.bool, some yes)] initialState
  let rawMap : SourceTypedRuntime.Value := .mapping (.comptime .bool) .bool []
  let emptyMap : SourceTypedRuntime.Value := .mapping .bool .bool []
  check compiled "nested" [yes, rawMap] yes
    [(.bool, some yes), (.mapping .bool .bool, some rawMap), (.bool, some yes),
      (.mapping .bool .bool, some emptyMap), (.bool, some no), (.bool, some yes), (.bool, some yes)] initialState
  check compiled "nested" [no, rawMap] yes
    [(.bool, some no), (.mapping .bool .bool, some rawMap), (.bool, some yes),
      (.mapping .bool .bool, none), (.bool, some yes), (.bool, none), (.bool, some yes)] initialState
  check compiled "shadow" [no] no
    [(.bool, some no), (.bool, some no), (.bool, some yes), (.bool, some no)] initialState
  check compiled "early" [no] yes
    [(.bool, some no), (.mapping .bool .bool, some emptyMap), (.bool, some no), (.word, none)] initialState
  check compiled "branchFault" [no] no
    [(.bool, some no), (.bool, some no), (.bool, none), (.bool, some no)] initialState
  let item ← SourceCoreUnifiedCorpusSupport.get "typed lexical named Item"
    (match compiled.sourceProgram.signatures.dataTypes.head? with | some item => Except.ok item | none => Except.error "no Item")
  check compiled "missing" [no] no [(.bool, some no), (.mapping .bool (.nominal item.id []), none)] initialState
  let identity ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "identity"
  let fn : SourceTypedRuntime.Value := .global identity []
  check compiled "callable" [fn, yes] fn
    [(.function .bool .bool, some fn), (.bool, some yes), (.function .bool .bool, some fn), (.function .bool .bool, some fn)] initialState
  check compiled "callable" [fn, no] fn
    [(.function .bool .bool, some fn), (.bool, some no), (.function .bool .bool, some fn)] initialState
  for name in ["conditionFault", "branchFault"] do
    let gap ← faultBinder compiled name "gap"
    for fuel in [0, 41, 300000] do
      match ← finished compiled name [yes] fuel initialState with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) s!"lexical fault changed its exact binder {name}"
        let cells := if name == "conditionFault" then [(.bool, some yes), (.bool, none)]
          else [(.bool, some yes), (.bool, some yes), (.bool, none), (.bool, some no)]
        assertCells initialState final cells name
      | other => throw (IO.userError s!"typed lexical named initializer/condition fault changed: {reprStr other}")
  for fuel in [0, 41, 300000] do
    match ← finished compiled "missing" [yes] fuel initialState with
    | .fault (.typeMismatch raw none) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (raw == .nominal item.id []) "lexical missing-default raw nominal metadata changed"
      assertCells initialState final
        [(.bool, some yes), (.mapping .bool raw, some (.mapping .bool raw [])), (.word, none)] "missing"
    | other => throw (IO.userError s!"typed lexical named missing default changed: {reprStr other}")
  IO.println "typed lexical named bodies: scoped bindings/return/fault, actual parameter order, raw mapping metadata and resume GREEN"

end Tests.SourceCoreTypedLexicalNamedParameters
end

section
-- leanmerge: from Solcore.Test.SourceCoreTypedLexicalWhile
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual lowering, checker receipts and independent source control connect to
the while theorem under arbitrary typed ambient captures. Runtime fixtures cover
lexical exits, condition/body faults, persistent effects and suspended continue. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace Tests.SourceCoreTypedLexicalWhile
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedLexicalWhile CompatiblePayload GeneralHeap ReadOnly
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"typed_while", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "typed_while.solc"⟩, 0, 1⟩
private def expression : ExpressionId := ⟨⟨owner, 0⟩⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index + 1⟩⟩
private def condition : ExpressionNode := {id := expression, span, type := .bool, form := .reference "true" (.builtinBoolean true)}
private def bodyNode : StatementNode := ⟨statement 0, span, .unit, .breakStmt⟩
private def whileNode : StatementNode := ⟨statement 1, span, .unit, .whileLoop expression [statement 0]⟩
private def returnNode : StatementNode := ⟨statement 2, span, .unit, .returnStmt none⟩
private def statements := [statement 1, statement 2]
private def source : TypedSource := {
  owner, inputs := [], roots := statements.map .statement,
  nodes := [.expression condition, .statement bodyNode, .statement whileNode, .statement returnNode]}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := SourceSemantics.Context.ofSignatures signatures
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def reason := Word.ofNatModulo 19
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem prepared : (SourceCoreCompatibleCatalog.prepare signatures 10 [.unit, .bool]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.unit, .bool]).toOption.get prepared
private def values := SourceCoreCompatibleValues.Context.initial checked
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def expressionPolicy := SourceCoreCompatibleDataExpressions.functionPolicy 10 values
private def onError (_ : SourceCoreAllocationLayouts.Error) : SourceCoreBasic.Error := .traversalExhausted (.declaration owner)
private def policy (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) : SourceCoreLoops.Policy := {
  lowerExpression := fun fuel source scope id reasonAt => SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody fuel compilation source scope id reasonAt
  readStatement := SourceCoreCompatibleDataExpressions.readStatement checked
  lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder checked
  sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt ⟨owner, []⟩ [] onError)) }
private def conditionCode := LanguageResult.success (.bool true)
private def loopCode := LocalLoop.whileLoop .unit conditionCode (LocalLoop.breaking .unit) reason
private def code := LocalLoop.sequence .unit loopCode (LocalLoop.returned .unit)
private theorem conditionGenerated : SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody 4 compilation source [] expression (fun _ => reason) = .ok ⟨.bool, conditionCode⟩ := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  rfl
private theorem generated (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) :
    SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 5 source [] statements .unit (fun _ => reason) true reason = .ok code := by
  change (do
    let condition ← SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody 4 compilation source [] expression (fun _ => reason)
    SourceCoreBasic.ensureType (.occurrence (statement 1).occurrence) .bool condition.type
    pure (LocalLoop.sequence .unit (LocalLoop.whileLoop .unit condition.expression (LocalLoop.breaking .unit) reason) (LocalLoop.returned .unit))) = .ok code
  rw [conditionGenerated]
  rfl
private theorem conditionTyped : ExpressionHasType source context expression .bool := by
  apply ExpressionHasType.ofOrdinary (node := condition) (rawType := .bool) (lookupExpression?_sound rfl)
    (.reference (.builtinBoolean true)) (.bool (TypeParameterBindersWellFormed.ofSignatures signatures)) (.bool (TypeParameterBindersWellFormed.ofSignatures signatures))
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem conditionSyntax : CompatibleExpressionTyped.Syntax source expression :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := condition) rfl (.bool _ _)))))))
private theorem conditionTree : CompatibleExpressionTyped.Tree 10 values source context [] (fun _ => reason) [] expression ⟨.bool, conditionCode⟩ := by
  exact CompatibleExpressionTyped.tree_of_functions (policy := expressionPolicy) (body := noBody) (context := compilation)
    (values := values) (scope := []) (sourceContext := context) (fuel := 4) unique
    (by intro id binder index type selected; cases selected) rfl rfl rfl
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (by
      intro id node _ found
      have member := (lookupExpression?_sound found).1
      simp [source] at member
      rcases member with rfl
      rfl)
    conditionSyntax rfl conditionTyped conditionGenerated

private theorem loopChecked (definitions : DataEnvironment) (administrative : Core.Context) :
    infer? administrative loopCode definitions = some (LocalLoop.resultType .unit) :=
  infer_complete (LocalLoop.whileLoop_hasType reason .unit (LanguageResult.success_hasType .bool) (LocalLoop.breaking_hasType .unit))

/-- Native typing comes from the actual checker at this loop site. The source
condition and body certificates are independently constructed. -/
private theorem certified (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout)
    (globals : Nat) (definitions : DataEnvironment) (administrative : Core.Context) {actual : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 5 source [] statements .unit (fun _ => reason) true reason = .ok actual) :
    Tree layouts ⟨owner, []⟩ [] frame globals onError 10 values source [] (fun _ => reason) definitions administrative
      context [] true statements .unit .unit actual := by
  have same := Except.ok.inj ((generated layouts frame globals).symm.trans accepted)
  subst actual
  exact .whileLoop (node := whileNode) (conditionNode := condition) rfl rfl rfl rfl conditionTree
    (.breaking (node := bodyNode) rfl rfl) (infer_sound (loopChecked definitions administrative))
    (.body (.body (.returnUnit (node := returnNode) [] rfl rfl rfl)) (.body (.returnUnit (node := returnNode) [] rfl rfl)))
private theorem valid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures]
  · intro requirement member; cases member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; cases member
private theorem sourceTrace (heap : Dynamic.Heap) : TypedScopedStatements.Executes true program context [] source [] heap statements context (.returned .unit) heap := by
  apply Dynamic.FunctionStatementsExecuteOutcome.control
  apply Dynamic.FunctionStatementsExecute.cons (middleContext := context) (nextEnvironment := []) (middle := heap)
  · apply Dynamic.StatementExecutes.whileLoop (outcome := .fallthrough []) (lookupStatement?_sound (node := whileNode) rfl) rfl
    apply Dynamic.WhileExecutes.breaks
    · exact .intro (lookupExpression?_sound (node := condition) rfl) (.builtinBoolean rfl) .nil
    · exact .terminal (.breakStmt (lookupStatement?_sound (node := bodyNode) rfl) rfl) (.breaking [])
  · exact .singleton (lookupStatement?_sound (node := returnNode) rfl) (by intro expression; simp [returnNode])
      (.returnUnit (lookupStatement?_sound (node := returnNode) rfl) rfl)

private def faults : FunctionCalls.FaultRep := fun _ _ => True

/-- Actual compiled while flow preserves an independent trace, with arbitrary
actual captures/renaming and a genuine live indexed context cell. -/
theorem compiled_preserves {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {actualCode : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 5 source [] statements .unit (fun _ => reason) true reason = .ok actualCode)
    {mapping world administrative actualContext canonical actual heap store ξ contextLocation native}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals []) (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (actualCode.rename ξ) value finalStore ∧
      FlowRep (values := values) (registry := values.registry) functions finalMap finalWorld faults .unit .unit (.returned .unit) value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld heap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap heap ∧
      TypedLexicalControl.LexicalResult checked ambient.definitions finalMap finalWorld administrative source.owner context [] [] context heap :=
  Tree.preserves (values := values) (ambient := ambient) (faults := faults) functions definitions registered (.refl _) program []
    (fun _ _ => trivial) (fun _ _ _ _ _ => trivial) (certified layouts frame globals _ _ accepted) valid unique environments heaps locals agrees typed reference read unmapped (sourceTrace heap)

/-- Completion alone reconstructs source while control and the lexical result;
there is no source-run, condition-run or body-run premise. -/
theorem compiled_reflects {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {actualCode : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 5 source [] statements .unit (fun _ => reason) true reason = .ok actualCode)
    {mapping world administrative actualContext canonical actual heap store ξ contextLocation native value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals []) (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (completed : Evaluates actual store (actualCode.rename ξ) value finalStore) :
    ∃ finalContext outcome after finalMap finalWorld,
      TypedScopedStatements.Executes true program context [] source [] heap statements finalContext outcome after ∧
      FlowRep (values := values) (registry := values.registry) functions finalMap finalWorld faults .unit .unit outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      TypedLexicalControl.LexicalResult checked ambient.definitions finalMap finalWorld administrative source.owner context [] [] finalContext after :=
  Tree.reflects (values := values) (ambient := ambient) (faults := faults) functions definitions registered (.refl _) program []
    (fun _ _ => trivial) (fun _ _ _ _ _ => trivial) (certified layouts frame globals _ _ accepted) valid unique environments heaps locals agrees typed reference read unmapped completed

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function falseLoop() returns (Word) { let x: Word = 7; while (false) { let skip: Word = 8; } return x; }",
    "function nestedBreak(flag: Bool) returns (Word) { let x: Word = 7; while (true) { let x: Word = 8; { let z: Word; if (flag) { break; } else { break; } } let skipped: Word = 9; } return x; }",
    "function earlyReturn() returns (Word) { while (true) { let x: Word = 11; return x; } let skipped: Word = 13; return skipped; }",
    "function conditionFault() returns (Word) { let absent: Bool; while (absent) { return 3; } return 7; }",
    "function bodyFault() returns (Word) { while (true) { let absent: Word; let failed: Word = absent; break; } return 7; }",
    "function lazyCondition() returns (Word) { let m: mapping(Bool => Bool); while (m[true]) { return 3; } return 7; }",
    "function spin() { while (true) { let retained: Word = 5; continue; } }"
  ]}] }

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "typed while source checker" (checkProgram workspace)
  let falseLoop ← SourceCompilerFeatureSupport.compileNamed checked "falseLoop"
  SourceCompilerFeatureSupport.require ((← falseLoop.run []) == SourceCompilerFeatureSupport.scalar 7) "false while executed its body"
  falseLoop.checkCells [] [(.word, some (SourceCompilerFeatureSupport.scalar 7))]
  falseLoop.checkResume [] (SourceCompilerFeatureSupport.scalar 7)
  let nested ← SourceCompilerFeatureSupport.compileNamed checked "nestedBreak"
  for flag in [false, true] do
    SourceCompilerFeatureSupport.require ((← nested.run [.bool flag]) == SourceCompilerFeatureSupport.scalar 7) "nested break lost outer scope"
    nested.checkCells [.bool flag] [(.bool, some (.bool flag)), (.word, some (SourceCompilerFeatureSupport.scalar 7)),
      (.word, some (SourceCompilerFeatureSupport.scalar 8)), (.word, none)]
    nested.checkResume [.bool flag] (SourceCompilerFeatureSupport.scalar 7)
  let returned ← SourceCompilerFeatureSupport.compileNamed checked "earlyReturn"
  SourceCompilerFeatureSupport.require ((← returned.run []) == SourceCompilerFeatureSupport.scalar 11) "loop return changed result"
  returned.checkCells [] [(.word, some (SourceCompilerFeatureSupport.scalar 11))]
  returned.checkResume [] (SourceCompilerFeatureSupport.scalar 11)
  let lazy ← SourceCompilerFeatureSupport.compileNamed checked "lazyCondition"
  SourceCompilerFeatureSupport.require ((← lazy.run []) == SourceCompilerFeatureSupport.scalar 7) "lazy loop condition changed default"
  lazy.checkCells [] [(.mapping .bool .bool, some (.mapping .bool .bool []))]
  lazy.checkResume [] (SourceCompilerFeatureSupport.scalar 7)
  for name in ["conditionFault", "bodyFault"] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    let outcome ← entry.invoke []
    match outcome.outcome with
    | .failed token _ =>
      match ← outcome.diagnostic token with
      | some {error := .uninitializedLocal _, span := some _, ..} => pure ()
      | _ => throw (IO.userError "while fault lost read location")
    | _ => throw (IO.userError "while fault unexpectedly completed")
    entry.checkCells [] [(if name == "conditionFault" then .bool else .word, none)]
  let spin ← SourceCompilerFeatureSupport.compileNamed checked "spin"
  let pending ← spin.invoke [] {executionFuel := 1000}
  match pending.outcome with
  | .outOfFuel checkpoint =>
      let resumed ← checkpoint.resume 1000
      match resumed with
      | .outOfFuel _ => pure ()
      | _ => throw (IO.userError "continue loop terminated after resume")
  | _ => throw (IO.userError "continue loop did not suspend")
  IO.println "typed lexical while: false/break/continue/return, scoped cells, lazy condition effects, faults and resume GREEN"
end Tests.SourceCoreTypedLexicalWhile
end

section
-- leanmerge: from Solcore.Test.SourceCoreTypedLexicalWhileNative
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual lowering, checker receipts and independent source control connect to
the while theorem under arbitrary typed ambient captures. Runtime fixtures cover
lexical exits, condition/body faults, persistent effects and suspended continue. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace Tests.SourceCoreTypedLexicalWhileNative
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedLexicalWhile CompatiblePayload GeneralHeap ReadOnly
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"typed_while", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "typed_while.solc"⟩, 0, 1⟩
private def expression : ExpressionId := ⟨⟨owner, 0⟩⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index + 1⟩⟩
private def condition : ExpressionNode := {id := expression, span, type := .bool, form := .reference "true" (.builtinBoolean true)}
private def bodyNode : StatementNode := ⟨statement 0, span, .unit, .breakStmt⟩
private def whileNode : StatementNode := ⟨statement 1, span, .unit, .whileLoop expression [statement 0]⟩
private def returnNode : StatementNode := ⟨statement 2, span, .unit, .returnStmt none⟩
private def ifNode : StatementNode := ⟨statement 3, span, .unit, .ifThen expression [statement 1] none⟩
private def blockNode : StatementNode := ⟨statement 4, span, .unit, .block [statement 3]⟩
private def statements := [statement 4, statement 2]
private def source : TypedSource := {
  owner, inputs := [], roots := statements.map .statement,
  nodes := [.expression condition, .statement bodyNode, .statement whileNode, .statement returnNode, .statement ifNode, .statement blockNode]}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := SourceSemantics.Context.ofSignatures signatures
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def reason := Word.ofNatModulo 19
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem prepared : (SourceCoreCompatibleCatalog.prepare signatures 10 [.unit, .bool]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.unit, .bool]).toOption.get prepared
private def values := SourceCoreCompatibleValues.Context.initial checked
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def expressionPolicy := SourceCoreCompatibleDataExpressions.functionPolicy 10 values
private def onError (_ : SourceCoreAllocationLayouts.Error) : SourceCoreBasic.Error := .traversalExhausted (.declaration owner)
private def policy (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) : SourceCoreLoops.Policy := {
  lowerExpression := fun fuel source scope id reasonAt => SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody fuel compilation source scope id reasonAt
  readStatement := SourceCoreCompatibleDataExpressions.readStatement checked
  lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder checked
  sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt ⟨owner, []⟩ [] onError)) }
private def conditionCode := LanguageResult.success (.bool true)
private def loopCode := LocalLoop.whileLoop .unit conditionCode (LocalLoop.breaking .unit) reason
private def ifCode := LocalLoop.sequence .unit
  (LocalLoop.conditional .unit conditionCode (LocalLoop.sequence .unit loopCode (LocalLoop.fallthrough .unit)) (LocalLoop.fallthrough .unit))
  (LocalLoop.fallthrough .unit)
private def code := LocalLoop.sequence .unit ifCode (LocalLoop.returned .unit)
private theorem conditionGenerated (fuel : Nat) : SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody (fuel + 1) compilation source [] expression (fun _ => reason) = .ok ⟨.bool, conditionCode⟩ := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  rfl
private theorem loopGenerated (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) :
    SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 6 source [] [statement 1] .unit (fun _ => reason) false reason =
      .ok (LocalLoop.sequence .unit loopCode (LocalLoop.fallthrough .unit)) := by
  change (do
    let condition ← SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody 5 compilation source [] expression (fun _ => reason)
    SourceCoreBasic.ensureType (.occurrence (statement 1).occurrence) .bool condition.type
    pure (LocalLoop.sequence .unit (LocalLoop.whileLoop .unit condition.expression (LocalLoop.breaking .unit) reason) (LocalLoop.fallthrough .unit))) = _
  rw [conditionGenerated]
  rfl
private theorem ifGenerated (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) :
    SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 7 source [] [statement 3] .unit (fun _ => reason) false reason = .ok ifCode := by
  change (do
    let condition ← SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody 6 compilation source [] expression (fun _ => reason)
    SourceCoreBasic.ensureType (.occurrence (statement 3).occurrence) .bool condition.type
    let yes ← SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 6 source [] [statement 1] .unit (fun _ => reason) false reason
    pure (LocalLoop.sequence .unit (LocalLoop.conditional .unit condition.expression yes (LocalLoop.fallthrough .unit)) (LocalLoop.fallthrough .unit))) = _
  rw [conditionGenerated, loopGenerated]
  rfl
private theorem generated (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) :
    SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 8 source [] statements .unit (fun _ => reason) true reason = .ok code := by
  change (do
    let body ← SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 7 source [] [statement 3] .unit (fun _ => reason) false reason
    pure (LocalLoop.sequence .unit body (LocalLoop.returned .unit))) = _
  rw [ifGenerated]
  rfl
private theorem conditionTyped : ExpressionHasType source context expression .bool := by
  apply ExpressionHasType.ofOrdinary (node := condition) (rawType := .bool) (lookupExpression?_sound rfl)
    (.reference (.builtinBoolean true)) (.bool (TypeParameterBindersWellFormed.ofSignatures signatures)) (.bool (TypeParameterBindersWellFormed.ofSignatures signatures))
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem conditionSyntax : CompatibleExpressionTyped.Syntax source expression :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := condition) rfl (.bool _ _)))))))
private theorem syntaxTree : TypedLexicalWhile.Syntax source context true statements .unit :=
  .block (node := blockNode) rfl rfl rfl
    (.ifThen (node := ifNode) (conditionNode := condition) rfl rfl rfl rfl rfl conditionTyped conditionSyntax
      (.whileLoop (node := whileNode) (conditionNode := condition) rfl rfl rfl rfl conditionTyped conditionSyntax
        (.breaking (node := bodyNode) rfl rfl) (.body (.body (.nil (.inl rfl)))))
      (.body (.body (.nil (.inl rfl)))) (.body (.body (.nil (.inl rfl)))))
    (.body (.body (.returnUnit (node := returnNode) [] rfl rfl rfl)))
private theorem codeTyped {definitions : DataEnvironment} {administrative : Core.Context} :
    HasType administrative code (LocalLoop.resultType .unit) definitions := by
  apply LocalLoop.sequence_hasType .unit
  · apply LocalLoop.sequence_hasType .unit
    · apply LocalLoop.conditional_hasType .unit (LanguageResult.success_hasType .bool)
      · exact LocalLoop.sequence_hasType .unit (LocalLoop.whileLoop_hasType reason .unit
          (LanguageResult.success_hasType .bool) (LocalLoop.breaking_hasType .unit)) (LocalLoop.fallthrough_hasType .unit)
      · exact LocalLoop.fallthrough_hasType .unit
    · exact LocalLoop.fallthrough_hasType .unit
  · exact LocalLoop.returned_hasType .unit

/-- Only the enclosing checker result is provided; there are no per-loop
native typing hypotheses. Blocks, conditionals and sequencing are inverted. -/
theorem extracted {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {definitions : DataEnvironment} {administrative : Core.Context} {actual : Expr} {nativeType : Ty}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 8 source [] statements .unit (fun _ => reason) true reason = .ok actual)
    (checked : infer? administrative actual definitions = some nativeType) :
    Tree layouts ⟨owner, []⟩ [] frame globals onError 10 values source [] (fun _ => reason) definitions administrative
      context [] true statements .unit .unit actual := by
  apply tree_of_typed_flow rfl (by intros; rfl) rfl ?_ syntaxTree rfl rfl rfl
    (by intro id binder index type found; cases found) rfl accepted (infer_sound checked)
  intro sourceContext closed residual signatures scope fuel id node lowered declarations syntaxValue found typed generated
  exact CompatibleExpressionTyped.tree_of_functions unique declarations signatures closed residual
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (by
      intro id node _ found
      have member := (lookupExpression?_sound found).1
      simp [source] at member
      rcases member with rfl
      rfl)
    syntaxValue found typed generated

/-- The concrete accepted fixture supplies the enclosing checker receipt. -/
theorem concrete (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout)
    (globals : Nat) (definitions : DataEnvironment) (administrative : Core.Context) :
    Tree layouts ⟨owner, []⟩ [] frame globals onError 10 values source [] (fun _ => reason) definitions administrative
      context [] true statements .unit .unit code :=
  extracted (generated layouts frame globals) (infer_complete codeTyped)

private def finished := LocalControl.finish .unit (LocalLoop.toControl .unit code reason) (LanguageResult.success .unit)

/-- The same automatic extraction also accepts the real finish/toControl body
and uses the enclosing checker result, without a flow or loop typing premise. -/
theorem extracted_finished {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {definitions : DataEnvironment} {administrative : Core.Context} {actual : Expr} {nativeType : Ty}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) 8 source [] statements .unit (fun _ => reason) reason reason = .ok actual)
    (checked : infer? administrative actual definitions = some nativeType) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 8 source [] statements .unit (fun _ => reason) true reason = .ok flow ∧
      Tree layouts ⟨owner, []⟩ [] frame globals onError 10 values source [] (fun _ => reason) definitions administrative
        context [] true statements .unit .unit flow ∧
      actual = LocalControl.finish .unit (LocalLoop.toControl .unit flow reason) (LanguageResult.success .unit) := by
  apply tree_of_typed_body rfl (by intros; rfl) rfl ?_ syntaxTree rfl rfl rfl
    (by intro id binder index type found; cases found) rfl accepted (infer_sound checked)
  intro sourceContext closed residual signatures scope fuel id node lowered declarations syntaxValue found typed generated
  exact CompatibleExpressionTyped.tree_of_functions unique declarations signatures closed residual
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (by
      intro id node _ found
      have member := (lookupExpression?_sound found).1
      simp [source] at member
      rcases member with rfl
      rfl)
    syntaxValue found typed generated

theorem concrete_finished (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout)
    (globals : Nat) (definitions : DataEnvironment) (administrative : Core.Context) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) 8 source [] statements .unit (fun _ => reason) true reason = .ok flow ∧
      Tree layouts ⟨owner, []⟩ [] frame globals onError 10 values source [] (fun _ => reason) definitions administrative
        context [] true statements .unit .unit flow ∧
      finished = LocalControl.finish .unit (LocalLoop.toControl .unit flow reason) (LanguageResult.success .unit) := by
  apply extracted_finished
  · unfold SourceCoreLoops.lowerStatementsWithPolicy
    rw [generated]
    rfl
  · exact infer_complete (LocalControl.finish_hasType .unit
      (LocalLoop.toControl_hasType reason .unit codeTyped) (LanguageResult.success_hasType .unit))

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function nested(flag: Bool) returns (Word) { let outer: Word = 17; { let unused: Bool; if (flag) { let inner: Word = 19; while (true) { let shadow: Word = 23; { while (true) { let stopped: Word; break; } } break; } } else { while (false) { let skipped: Word; } } } return outer; }",
    "function early() returns (Word) { let root: Word; { while (true) { let answer: Word = 31; if (true) { return answer; } continue; } } return 1; }"
  ]}] }
def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "native while source" (checkProgram workspace)
  let nested ← SourceCompilerFeatureSupport.compileNamed checked "nested"
  for flag in [false, true] do
    SourceCompilerFeatureSupport.require ((← nested.run [.bool flag]) == SourceCompilerFeatureSupport.scalar 17) "nested typed loop changed outer value"
    nested.checkResume [.bool flag] (SourceCompilerFeatureSupport.scalar 17)
    nested.checkCells [.bool flag] ([ (.bool, some (.bool flag)), (.word, some (SourceCompilerFeatureSupport.scalar 17)), (.bool, none)] ++
      if flag then [(.word, some (SourceCompilerFeatureSupport.scalar 19)), (.word, some (SourceCompilerFeatureSupport.scalar 23)), (.word, none)] else [])
  let early ← SourceCompilerFeatureSupport.compileNamed checked "early"
  SourceCompilerFeatureSupport.require ((← early.run []) == SourceCompilerFeatureSupport.scalar 31) "nested return changed result"
  early.checkCells [] [(.word, none), (.word, some (SourceCompilerFeatureSupport.scalar 31))]
  early.checkResume [] (SourceCompilerFeatureSupport.scalar 31)
  IO.println "native while extraction: whole checker to loop sites, nested lexical/control wrappers and resume GREEN"
end Tests.SourceCoreTypedLexicalWhileNative
end

section
-- leanmerge: from Solcore.Test.SourceCoreTypedMixedNamedParameters
#check_failure Solcore.SourceSemantics.CoreLowering.TypedMixedNamedBody.Certificate.mk
#check_failure Solcore.SourceSemantics.CoreLowering.TypedMixedNamedParameters.Entry.mk
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! A static mixed-body receipt and an independent initializer-fault trace
retain the context before the failed declaration. Checked cached calls retain
ordered parameter/local cells, raw mapping metadata and real Core resumption. -/
set_option autoImplicit false
namespace Tests.SourceCoreTypedMixedNamedParameters
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedMixedNamedBody

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"typed_mixed_named", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "mixed_named.solc"⟩, 0, 1⟩
private def expression : ExpressionId := ⟨⟨owner, 0⟩⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def binder (index : Nat) : TypedBinder := ⟨⟨owner, index⟩, "value", .mono .bool, [], false, none⟩
private def absentNode : ExpressionNode := {
  id := expression, span, type := .bool, form := .reference "value" (.local (binder 0).id) }
private def first : StatementNode := ⟨statement 0, span, .unit, .letDecl (binder 0) none⟩
private def second : StatementNode := ⟨statement 1, span, .unit, .letDecl (binder 1) (some expression)⟩
private def returned : StatementNode := ⟨statement 2, span, .unit, .returnStmt none⟩
private def statements := [statement 0, statement 1, statement 2]
private def source : TypedSource := {
  owner, inputs := [], roots := statements.map .statement,
  nodes := [.expression absentNode, .statement first, .statement second, .statement returned] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def initial := SourceSemantics.Context.ofSignatures signatures
private def entered := initial.withLocal (binder 0).id (binder 0).scheme
private def complete := entered.withLocal (binder 1).id (binder 1).scheme
private theorem firstExtension : BinderExtends owner initial (binder 0) entered := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {binders := .ofSignatures signatures, quantified_nodup := by simp [binder, TypeSystem.Scheme.mono], body := .builtin .bool}
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl }
  · simp [LocalFresh, initial, SourceSemantics.Context.ofSignatures]
private theorem secondExtension : BinderExtends owner entered (binder 1) complete := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {binders := (TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _, quantified_nodup := by simp [binder, TypeSystem.Scheme.mono], body := .builtin .bool}
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl }
  · simp [LocalFresh, entered, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder]
private theorem absentTyped : ExpressionHasType source entered expression .bool := by
  have admitted : TypeAdmissible entered .bool := .bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _)
  apply ExpressionHasType.ofOrdinary (node := absentNode) (rawType := .bool) (lookupExpression?_sound rfl)
    (.reference (.local .head .head (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible admitted) []
      .empty (by intro metavariable replacement member; cases member) (SchemeInstantiates.empty_apply _)
      (by simp) (by intro _ member; cases member) .nil))) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem absentSyntax : CompatibleExpressionTyped.Syntax source expression :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.read (node := absentNode) rfl rfl))))))
private theorem syntaxTree : TypedStatementMixed.Syntax source initial statements .unit :=
  .uninitialized (node := first) rfl rfl rfl rfl firstExtension (by decide)
    (.initialized (node := second) (initializerNode := absentNode) rfl rfl rfl rfl secondExtension (by decide)
      rfl rfl absentTyped absentSyntax (.body (.returnUnit (node := returned) [] rfl rfl rfl)))
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private def compilation (plan : SourceSpecializationWorklist.Plan) : SourceCoreFunctions.Context := {
  plan, owner := ⟨owner, []⟩, globals := [], administrativePrefix := 1, solvedRequirements := [], internalReason := Word.zero }
private def policy (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout)
    (globals : Nat) (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (program : CheckedProgram) (representation : SourceCoreGeneralFunctions.Representation)
    (plan : SourceSpecializationWorklist.Plan) (values : SourceCoreCompatibleValues.Context)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program) : SourceCoreLoops.Policy := {
  lowerExpression := SourceCoreGeneralFunctions.lowerContextualExpression program representation program.signatures
    ⟨[]⟩ [] assignments diagnostics (compilation plan) none none none
  readStatement := SourceCoreCompatibleDataExpressions.readStatement values.checked
  lowerBinder := SourceCoreGeneralFunctions.contextualBinder representation ⟨[]⟩ ⟨owner, []⟩ []
  sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt ⟨owner, []⟩ [] onError)) }

/-- Actual contextual success supplies both let receipts and the remaining
body tree. The static premises contain no child/body semantic theorem. -/
theorem mixed_certificate (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout)
    (globals : Nat) (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (program : CheckedProgram) (representation : SourceCoreGeneralFunctions.Representation)
    (plan : SourceSpecializationWorklist.Plan) (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (sourceSignatures : initial.signatures = values.checked.signatures)
    (readExpression : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (lowerBinder : representation.expressions.lowerBinder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked)
    {fuel : Nat} {code : Expr} (fellThrough escaped : Word)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy
      (policy layouts frame globals onError program representation plan values assignments diagnostics) fuel
      source [] statements .unit (fun _ => Word.zero) fellThrough escaped = .ok code) :
    Nonempty (Certificate layouts ⟨owner, []⟩ [] frame globals onError readFuel values source initial []
      (fun _ => Word.zero) [] statements .unit .unit
      (policy layouts frame globals onError program representation plan values assignments diagnostics) fuel fellThrough escaped code) := by
  apply of_contextual (locals := ⟨[]⟩) (compilation := compilation plan)
      (native := none) (parent := none) (skipInitializer := none) ?_ unique rfl rfl ?_ sourceSignatures
      readExpression lowerRead leafLowerer rfl lowerBinder rfl rfl rfl syntaxTree rfl accepted
  · constructor
    · intro id node _ found
      have member := (lookupExpression?_sound found).1
      simp [source] at member
      subst node
      rfl
    · intro id node _ found
      have member := (lookupExpression?_sound found).1
      simp [source] at member
      subst node
      rfl
    · intros; rfl
    · intros; rfl
  · intro id declared index type selected authentic
    cases selected

private def closure : Dynamic.Closure := ⟨[], .unit, statements, source, [], initial, []⟩
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def faultHeap : Dynamic.Heap := ⟨[⟨.bool, none, none⟩]⟩

/-- The independent source fault occurs in `entered`, before `complete` exists.
It connects directly to the function body trace used by the named bridge. -/
theorem initializer_fault :
    Dynamic.FunctionStatementsFault program initial [] source [] ⟨[]⟩ statements entered
      (.uninitializedLocation ⟨0⟩) faultHeap ∧
    FunctionCallBody.Trace program closure initial [] ⟨[]⟩ (.fault (.uninitializedLocation ⟨0⟩)) faultHeap ∧
    entered ≠ complete := by
  have failed : Dynamic.FunctionStatementsFault program initial [] source [] ⟨[]⟩ statements entered
      (.uninitializedLocation ⟨0⟩) faultHeap := by
    apply Dynamic.FunctionStatementsFault.tail
      (Dynamic.StatementExecutes.letUninitialized (node := first) (lookupStatement?_sound rfl) rfl rfl firstExtension .append)
    apply Dynamic.FunctionStatementsFault.head
    apply Dynamic.StatementFaults.letInitializer (node := second) (lookupStatement?_sound rfl) rfl rfl
    apply Dynamic.ExpressionFaults.form (node := absentNode) (lookupExpression?_sound rfl)
    exact .localUninitialized (owned := []) (coercions := []) (cell := ⟨.bool, none, none⟩)
      rfl .head (.intro .head) rfl rfl (by rintro ⟨key, value, impossible⟩; cases impossible)
  refine ⟨failed, .fault failed, ?_⟩
  intro same
  have impossible : 1 = 2 := congrArg (fun context => context.locals.length) same
  omega

private def content : String := String.intercalate "\n" [
  "enum Item { Item(Bool) }",
  "function mixed(flag: Bool, value: Word) returns (Bool) { let unused: Word; let first = flag; let absent: Bool; let last = !first; return last; }",
  "function lazy(flag: Bool) returns (Bool) { let before: Word; let m: mapping(Bool => Bool); let first = m[flag]; let gap: Bool; let last = m[!flag]; return first || last; }",
  "function nested(m: mapping(Bool => mapping(Bool => Bool)), flag: Bool) returns (Bool) { let before: Word; let first = m[flag][false]; let gap: Bool; let last = !m[!flag][true]; return first ? first : last; }",
  "function early(flag: Bool) returns (Bool) { let first = flag; let gap: Word; return first; let unreachable: Word; }",
  "function absent(flag: Bool) returns (Bool) { let first = flag; let gap: Bool; let failed = gap; let unreachable = true; return unreachable; }",
  "function missing(flag: Bool) returns (Bool) { let first = flag; let gap: Word; let m: mapping(Bool => Item); let failed = m[flag]; return true; }",
  "function identity(flag: Bool) returns (Bool) { return flag; }",
  "function callable(f: function(Bool) returns (Bool), flag: Bool) returns (function(Bool) returns (Bool)) { let gap: Word; let saved = f; let same = saved; return same; }"
]

private def finished (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initialState : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let firstResult ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initialState
  let result ← SourceCoreUnifiedCorpusSupport.get "typed mixed named resume" (SourceCoreUnifiedCompilation.Result.resume firstResult 300000)
  pure result.observation

private def check (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (expected : SourceTypedRuntime.Value)
    (cells : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (initialState : SourceTypedRuntime.RuntimeState) : IO Unit := do
  for fuel in [0, 41, 300000] do
    match ← finished compiled name arguments fuel initialState with
    | .done value final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr expected) s!"typed mixed named result changed {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initialState.heap.length) == reprStr initialState.heap)
        s!"typed mixed named prefix changed {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initialState.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr cells)
        s!"typed mixed named ordered cells changed {name}: {reprStr final.heap}"
      SourceCoreUnifiedCorpusSupport.assertTrue (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
        s!"typed mixed named unsafe final heap {name}"
    | other => throw (IO.userError s!"typed mixed named failed {name}: {reprStr other}")

private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name localName : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "typed mixed named fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == localName) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "typed mixed named exact binder missing")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "typed mixed named bodies" content
    ["mixed", "lazy", "nested", "early", "absent", "missing", "identity", "callable"]
  let initialState : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩,
    ⟨.word, some (.word (Word.ofNatModulo 731))⟩]}
  let flag : SourceTypedRuntime.Value := .bool false
  let seven : SourceTypedRuntime.Value := .word (Word.ofNatModulo 7)
  check compiled "mixed" [flag, seven] (.bool true)
    [(.bool, some flag), (.word, some seven), (.word, none), (.bool, some flag), (.bool, none), (.bool, some (.bool true))] initialState
  let emptyMap : SourceTypedRuntime.Value := .mapping .bool .bool []
  check compiled "lazy" [flag] flag
    [(.bool, some flag), (.word, none), (.mapping .bool .bool, some emptyMap), (.bool, some flag), (.bool, none), (.bool, some flag)] initialState
  let rawMap : SourceTypedRuntime.Value := .mapping (.comptime .bool) (.mapping .bool .bool) []
  check compiled "nested" [rawMap, flag] (.bool true)
    [(.mapping .bool (.mapping .bool .bool), some rawMap), (.bool, some flag), (.word, none), (.bool, some flag), (.bool, none), (.bool, some (.bool true))] initialState
  check compiled "early" [flag] flag [(.bool, some flag), (.bool, some flag), (.word, none)] initialState
  let identity ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "identity"
  let fn : SourceTypedRuntime.Value := .global identity []
  check compiled "callable" [fn, flag] fn
    [(.function .bool .bool, some fn), (.bool, some flag), (.word, none), (.function .bool .bool, some fn), (.function .bool .bool, some fn)] initialState
  let gap ← faultBinder compiled "absent" "gap"
  for fuel in [0, 41, 300000] do
    match ← finished compiled "absent" [flag] fuel initialState with
    | .fault (.uninitializedLocal actual) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) "failed initializer changed its exact fault binder"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initialState.heap.length).map (fun cell => (cell.type, cell.value))) ==
        reprStr ([ (.bool, some flag), (.bool, some flag), (.bool, none)] : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)))
        "failed initializer allocated a binder or changed preceding source cells"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initialState.heap.length) == reprStr initialState.heap)
        "failed initializer changed the inert prefix"
    | other => throw (IO.userError s!"typed mixed named initializer fault changed: {reprStr other}")
    match ← finished compiled "missing" [flag] fuel initialState with
    | .fault (.typeMismatch raw none) final =>
      let item ← SourceCoreUnifiedCorpusSupport.get "typed mixed named Item"
        (match compiled.sourceProgram.signatures.dataTypes.head? with | some item => Except.ok item | none => Except.error "no Item")
      SourceCoreUnifiedCorpusSupport.assertTrue (raw == .nominal item.id []) "missing-default raw result metadata changed"
      SourceCoreUnifiedCorpusSupport.assertTrue (final.heap.length == initialState.heap.length + 4)
        "missing-default initializer allocated its failed binder"
      match (final.heap.drop initialState.heap.length)[3]? with
      | some cell =>
        match cell.type, cell.value with
        | .mapping .bool valueType, some (.mapping .bool valueMetadata []) =>
          SourceCoreUnifiedCorpusSupport.assertTrue (valueType == raw && valueMetadata == raw)
            "lazy mapping initialization lost raw nominal metadata"
        | _, _ => throw (IO.userError s!"missing-default source mapping changed: {reprStr cell}")
      | none => throw (IO.userError "missing-default source mapping disappeared")
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initialState.heap.length) == reprStr initialState.heap)
        "missing-default initializer changed the inert prefix"
    | other => throw (IO.userError s!"typed mixed named missing default changed: {reprStr other}")
  IO.println "typed mixed named bodies: reached contexts, parameter/local order, lazy nested mappings, callable aliases, exact initializer faults and resume GREEN"

end Tests.SourceCoreTypedMixedNamedParameters
end

section
-- leanmerge: from Solcore.Test.SourceCoreTypedNamedParameters
#check_failure Solcore.SourceSemantics.CoreLowering.TypedNamedBody.Certificate.mk
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Static zero-parameter compilation receipts and concrete checked source
regressions. Semantic certificates are extracted at one actual body context;
neither a universal body IH nor a finite source execution is a static premise. -/
set_option autoImplicit false
namespace Tests.SourceCoreTypedNamedParameters
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedNamedBody

private def source (owner : Resolved.DeclarationId) : TypedSource := {
  owner, inputs := [], roots := [], nodes := [] }
private def compilation (plan : SourceSpecializationWorklist.Plan)
    (owner : SourceSpecialization.SpecializationKey) : SourceCoreFunctions.Context := {
  plan, owner, globals := [], administrativePrefix := 1, solvedRequirements := [], internalReason := Word.zero }
private def policy (program : CheckedProgram) (representation : SourceCoreGeneralFunctions.Representation)
    (plan : SourceSpecializationWorklist.Plan) (owner : SourceSpecialization.SpecializationKey)
    (values : SourceCoreCompatibleValues.Context)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program) :
    SourceCoreLoops.Policy := {
  lowerExpression := SourceCoreGeneralFunctions.lowerContextualExpression program representation program.signatures
    ⟨[]⟩ [] assignments diagnostics (compilation plan owner) none none none
  readStatement := SourceCoreCompatibleDataExpressions.readStatement values.checked
}
private def code (fellThrough escaped : Word) : Expr :=
  TypedStatements.finish .unit (LocalLoop.fallthrough .unit) fellThrough escaped

/-- The typed named body uses the actual contextual compiler and explicit
source context. No `BodyPreserves` or `BodyReflects` premise is hidden here. -/
theorem nil_certificate (program : CheckedProgram) (representation : SourceCoreGeneralFunctions.Representation)
    (plan : SourceSpecializationWorklist.Plan) (owner : SourceSpecialization.SpecializationKey)
    (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (context : SourceSemantics.Context) (fellThrough escaped : Word)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (readExpression : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values) :
    Nonempty (Certificate readFuel values (source owner.declaration) context [] (fun _ => Word.zero) [] [] .unit .unit
      (policy program representation plan owner values assignments diagnostics) 10 fellThrough escaped (code fellThrough escaped)) := by
  apply of_contextual (locals := ⟨[]⟩) (compilation := compilation plan owner)
      (native := none) (parent := none) (skipInitializer := none) ?_ ?_ closed residual ?_ sourceSignatures
      readExpression lowerRead leafLowerer rfl rfl .nil rfl rfl
  · constructor
    · intro id node _ found
      change none = some node at found; cases found
    · intro id node _ found
      change none = some node at found; cases found
    · intros; rfl
    · intros; rfl
  · cbv; decide
  · intro binder declared index native selected accepted
    cases selected

example (environment : Environment) (store : Store) (fellThrough escaped : Word) :
    Evaluates environment store (code fellThrough escaped) (.inRight .word .unit) store := by
  exact LocalControl.finish_fallthrough .unit
    (LocalLoop.toControl_normal .unit escaped (LocalLoop.fallthrough_evaluates .unit environment store))
    (by simpa [LanguageResult.success, Expr.weakenAt] using
      (show Evaluates (.unit :: .inLeft .unit .unit :: environment) store (.inRight .word .unit)
        (.inRight .word .unit) store from .inRight .unit))

private def content : String := String.intercalate "\n" [
  "enum Item { Item(Word) }",
  "function empty(flag: Bool, value: Word) { }",
  "function repeated(m: mapping(Bool => Bool)) returns (Bool) { m[true]; return m[false]; }",
  "function nested(m: mapping(Bool => mapping(Bool => Bool))) returns (Bool) { (m[true][false], !m[false][true]); return m[false][false] ? m[true][true] : !m[true][false]; }",
  "function early(m: mapping(Bool => Item)) returns (Bool) { return true; m[true]; }",
  "function firstFault(m: mapping(Bool => Item)) returns (Bool) { m[true]; return false; }",
  "function identity(flag: Bool) returns (Bool) { return flag; }",
  "function keep(f: function(Bool) returns (Bool), flag: Bool) returns (function(Bool) returns (Bool)) { flag; return f; }"
]

private def check (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (expected : SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) : IO Unit := do
  for fuel in [0, 39, 300000] do
    let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
    let result ← SourceCoreUnifiedCorpusSupport.get "typed named parameter resume" (SourceCoreUnifiedCompilation.Result.resume first 300000)
    match result.observation with
    | .done value final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr expected) s!"typed named result changed {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
        s!"typed named inert prefix changed {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue (final.heap.length == initial.heap.length + arguments.length)
        s!"typed named parameter count changed {name}"
    | other => throw (IO.userError s!"typed named execution failed {name}: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "typed named bodies" content
    ["empty", "repeated", "nested", "early", "firstFault", "identity", "keep"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩,
    ⟨.word, some (.word (Word.ofNatModulo 731))⟩]}
  check compiled "empty" [.bool false, .word (Word.ofNatModulo 7)] .unit initial
  let mapping : SourceTypedRuntime.Value := .mapping (.comptime .bool) .bool []
  check compiled "repeated" [mapping] (.bool false) initial
  check compiled "nested" [.mapping .bool (.mapping .bool .bool) []] (.bool true) initial
  let item ← SourceCoreUnifiedCorpusSupport.get "typed named Item"
    (match compiled.sourceProgram.signatures.dataTypes.head? with
      | some item => Except.ok item
      | none => Except.error "no data signature")
  let missing : SourceTypedRuntime.Value := .mapping .bool (.nominal item.id []) []
  check compiled "early" [missing] (.bool true) initial
  let identity ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "identity"
  check compiled "keep" [.global identity [], .bool false] (.global identity []) initial
  for fuel in [0, 39, 300000] do
    let first ← SourceCoreUnifiedCorpusSupport.execute compiled "firstFault" [missing] fuel initial
    let result ← SourceCoreUnifiedCorpusSupport.get "typed named fault resume" (SourceCoreUnifiedCompilation.Result.resume first 300000)
    match result.observation with
    | .fault (.typeMismatch expected none) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr expected == reprStr (.nominal item.id [] : TypeSystem.Ty))
        "typed named missing-default type changed"
      SourceCoreUnifiedCorpusSupport.assertTrue (final.heap.length == initial.heap.length + 1)
        "typed named missing-default parameter allocation changed"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap[initial.heap.length]?.map (·.value)) == reprStr (some (some missing)))
        "typed named fault changed its mapping parameter"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
        "typed named fault changed inert prefix"
    | other => throw (IO.userError s!"typed named first fault changed: {reprStr other}")
  IO.println "typed named bodies and parameter prefixes: nested indices, raw mapping, callable, early return, exact fault and resume GREEN"

end Tests.SourceCoreTypedNamedParameters
end

section
-- leanmerge: from Solcore.Test.SourceCoreTypedScopedControl
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual scoped block and conditional lowering supplies the full recursive
certificate. The independent trace includes lazy mapping initialization in a
block, a false condition with no else, and a subsequent explicit return. Native
condition and sequence slots carry typed captures and preserve resume effects. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreTypedScopedControl
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedScopedControl
open TypedScopedStatements (Executes FlowRep)
open CompatiblePayload GeneralHeap ReadOnly
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"typed_scoped_control", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "typed_scoped_control.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def mappingType : TypeSystem.Ty := .mapping .bool .bool
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "table", .mono mappingType, [], false, none⟩
private def baseNode : ExpressionNode := { id := id 0, span, type := mappingType, form := .reference "table" (.local binder.id) }
private def keyNode : ExpressionNode := { id := id 1, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def indexNode : ExpressionNode := { id := id 2, span, type := .bool, form := .index (id 0) (id 1) }
private def statement (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def discarded : StatementNode := ⟨statement 0, span, .unit, .expression (id 2) true⟩
private def scopedBlock : StatementNode := ⟨statement 1, span, .unit, .block [statement 0]⟩
private def branchReturn : StatementNode := ⟨statement 2, span, .bool, .returnStmt (some (id 1))⟩
private def conditional : StatementNode := ⟨statement 3, span, .unit, .ifThen (id 2) [statement 2] none⟩
private def finalReturn : StatementNode := ⟨statement 4, span, .bool, .returnStmt (some (id 1))⟩
private def statements := [statement 1, statement 3, statement 4]
private def source : TypedSource := {
  owner, inputs := [binder], roots := statements.map .statement,
  nodes := [.expression baseNode, .expression keyNode, .expression indexNode, .statement discarded,
    .statement scopedBlock, .statement branchReturn, .statement conditional, .statement finalReturn] }
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem metadata {expression : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp [source] at member
  rcases member with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem boolAdmitted : TypeAdmissible context .bool :=
  .bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme)
private theorem mappingAdmitted : TypeAdmissible context mappingType := .mapping boolAdmitted boolAdmitted
private theorem baseTyped : ExpressionHasType source context (id 0) mappingType := by
  apply ExpressionHasType.ofOrdinary (node := baseNode) (rawType := mappingType) (lookupExpression?_sound (by rfl))
    (.reference (.local (.head) (.head) (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible mappingAdmitted) []
      .empty (by intro metavariable replacement member; cases member) (by exact SchemeInstantiates.empty_apply mappingType)
      (by simp) (by intro _ member; cases member) (.nil)))) mappingAdmitted mappingAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem keyTyped : ExpressionHasType source context (id 1) .bool := by
  apply ExpressionHasType.ofOrdinary (node := keyNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean true)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexTyped : ExpressionHasType source context (id 2) .bool := by
  apply ExpressionHasType.ofOrdinary (node := indexNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.index baseTyped keyTyped) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexSyntax : CompatibleExpressionTyped.Syntax source (id 2) :=
  .index (node := indexNode) (keyNode := keyNode) (by cbv) rfl (by cbv) .bool
    (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.read (node := baseNode) rfl rfl)))))))
    (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := keyNode) rfl (.bool _ _))))))))
private theorem keySyntax : CompatibleExpressionTyped.Syntax source (id 1) :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := keyNode) rfl (.bool _ _)))))))
private theorem sourceSyntax (mode : Bool) : TypedScopedControl.Syntax source context mode statements .bool := by
  apply Syntax.block (node := scopedBlock) rfl rfl rfl
  · exact .fragment (.discard (node := discarded) (expressionNode := indexNode) rfl rfl rfl rfl rfl
      indexTyped indexSyntax (.nil (.inl rfl)))
  · apply Syntax.ifThen (node := conditional) (conditionNode := indexNode) rfl rfl rfl rfl rfl indexTyped indexSyntax
    · exact .fragment (.returnValue (node := branchReturn) (expressionNode := keyNode) [] rfl rfl rfl rfl rfl keyTyped keySyntax)
    · exact .fragment (.nil (.inl rfl))
    · exact .fragment (.returnValue (node := finalReturn) (expressionNode := keyNode) [] rfl rfl rfl rfl rfl keyTyped keySyntax)
private theorem contextValid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal]
  · intro requirement member; cases member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; cases member
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType]).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private theorem nativeExists : (checked.catalog.project mappingType).toOption.isSome = true := by cbv
private def nativeType := (checked.catalog.project mappingType).toOption.get nativeExists
private theorem projected : checked.catalog.project mappingType = .ok nativeType := by cbv
private def scope : SourceCoreLocalCell.Scope := [(binder.id, nativeType)]
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source scope context := by
  intro actual declared index native selected accepted
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst actual
    have actual : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder := by rfl
    rw [actual] at accepted
    cases accepted
    exact .head
  · simp at selected
private abbrev expressionPolicy := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
private def policy : SourceCoreLoops.Policy := {
  lowerExpression := fun fuel source scope expression reasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody fuel compilation source scope expression reasonAt
  readStatement := SourceCoreCompatibleDataExpressions.readStatement checked }
private theorem certified {mode : Bool} {code : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy 12 source scope statements .bool (fun _ => reason) mode reason = .ok code) :
    Tree 100 values source context [] (fun _ => reason) scope mode statements .bool .bool code := by
  apply tree_of_flow rfl ?_ (sourceSyntax mode) rfl accepted
  intro budget expression node lowered childSyntax found typed generated
  exact CompatibleExpressionTyped.tree_of_functions unique declarations rfl rfl rfl
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ (fun _ _ _ found => (metadata found).2)
    childSyntax found typed generated

private def compiledResult (mode : Bool) := SourceCoreLoops.lowerFlowStatementsWithPolicy policy 12 source scope statements
  .bool (fun _ => reason) mode reason
private def frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [frameLayout.definition]
private def functions : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def model := CompatibleAmbientHeap.payloadModel checked values.registry functions
private def faults : FunctionCalls.FaultRep := fun error token =>
  ((∃ location, error = .uninitializedLocation location) ∧ token = reason) ∨
  (∃ key value tag, MetadataRep values.registry (.mapping key value) tag ∧ error = .missingMappingDefault value ∧ token = reason.add tag)
private theorem uninitialized : ∀ (id : ExpressionId) location, faults (.uninitializedLocation location) ((fun _ => reason) id) :=
  fun _ location => .inl ⟨⟨location, rfl⟩, rfl⟩
private theorem missing : ∀ (id : ExpressionId) key value tag, MetadataRep values.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) (((fun _ => reason) id).add tag) :=
  fun _ key value tag owned => .inr ⟨key, value, tag, owned, rfl, rfl⟩
private def administrativeType : Ty := .function .unit frameLayout.type
private def administrativeValue : Value := .closure .unit frameLayout.type (.var 1) [SourceCoreCallableIndexedFrames.encode frameLayout .empty]
private theorem frameRegistered : frameLayout.Registered ambient.definitions := by
  constructor
  simp [ambient, AmbientDefinitions.append, frameLayout]
private theorem administrativeTyped : RuntimeValueHasType [] administrativeValue administrativeType ambient.definitions :=
  .closure (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed [] frameRegistered .empty) .nil) (.var rfl)
private def world : StoreTyping := [administrativeType, OptionalCell.cellType nativeType]
private def store : Store := [administrativeValue, .inLeft nativeType .unit]
private def environment : Environment := [.cellRef (OptionalCell.cellType nativeType) 1]
private def sourceEnvironment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def before : Dynamic.Heap := ⟨[⟨mappingType, none, none⟩]⟩
private def after : Dynamic.Heap := ⟨[⟨mappingType, some (.mapping .bool .bool []), none⟩]⟩
private theorem initial : GenericHeap.HeapRepresents model [1] world before store ∧
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) [1] world [] scope sourceEnvironment environment ambient.definitions := by
  have empty := (GenericHeap.HeapRepresents.empty (model := model)).allocate_administrative administrativeTyped
  obtain ⟨heap, reference⟩ := empty.allocate (.uninitialized projected) Dynamic.Heap.Allocates.append
  exact ⟨heap, .cons reference (.nil .nil)⟩
private theorem locals : Dynamic.EnvironmentAgrees before context.locals sourceEnvironment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem actualTyped : RuntimeEnvironmentHasTypes world (.integer 99 :: administrativeValue :: environment)
    [.integer, administrativeType, .cell (OptionalCell.cellType nativeType)] ambient.definitions :=
  .cons .integer (.cons (administrativeTyped.weaken ⟨world, rfl⟩) (.cons (.cellRef rfl) .nil))
private def ξ : Renaming := Renaming.comp (Renaming.insertion 0) (Renaming.insertion 0)
private theorem agrees : EnvironmentsAgree ξ environment (.integer 99 :: administrativeValue :: environment) :=
  GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix (show EnvironmentsAgree Renaming.id environment environment from fun {_ _} found => found) administrativeValue) (.integer 99)
private theorem initialRead : Dynamic.ExpressionEvaluatesOutcome program context [] source sourceEnvironment before (id 2) (.value (.bool false)) after := by
  apply Dynamic.ExpressionEvaluatesOutcome.value
  apply Dynamic.ExpressionEvaluates.intro (raw := .bool false) (middle := after) (lookupExpression?_sound (node := indexNode) (by cbv))
  · change Dynamic.ExpressionFormEvaluates program context [] source sourceEnvironment before (.index (id 0) (id 1)) [] [] (.bool false) after
    apply Dynamic.ExpressionFormEvaluates.indexDefault (coercions := []) rfl
    · exact .intro (lookupExpression?_sound (node := baseNode) (by rfl))
        (.localEmptyMapping rfl .head (.intro .head) rfl rfl rfl (.intro (.intro .head) .head)) .nil
    · exact .intro (lookupExpression?_sound (node := keyNode) (by cbv)) (.builtinBoolean rfl) .nil
    · exact .nil
    · exact .bool
  · exact .nil

private def sourceOutcome (_mode : Bool) : Dynamic.ControlOutcome := .returned (.bool true)
private theorem sourceTrace (mode : Bool) : Executes mode program context [] source sourceEnvironment before
    statements context (sourceOutcome mode) after := by
  have first : Dynamic.ExpressionEvaluates program context [] source sourceEnvironment before (id 2) (.bool false) after := by
    cases initialRead with | value evaluated => exact evaluated
  have second : Dynamic.ExpressionEvaluates program context [] source sourceEnvironment after (id 2) (.bool false) after := by
    apply Dynamic.ExpressionEvaluates.intro (raw := .bool false) (middle := after) (lookupExpression?_sound (node := indexNode) rfl)
    · apply Dynamic.ExpressionFormEvaluates.indexDefault (coercions := []) rfl
      · exact .intro (lookupExpression?_sound (node := baseNode) rfl) (.local rfl .head (.intro .head) rfl rfl) .nil
      · exact .intro (lookupExpression?_sound (node := keyNode) rfl) (.builtinBoolean rfl) .nil
      · exact .nil
      · exact .bool
    · exact .nil
  have returned : Dynamic.ExpressionEvaluates program context [] source sourceEnvironment after (id 1) (.bool true) after :=
    .intro (lookupExpression?_sound (node := keyNode) rfl) (.builtinBoolean rfl) .nil
  have blockTrace : Dynamic.StatementExecutes program context [] source sourceEnvironment before (statement 1)
      context (.fallthrough sourceEnvironment) after :=
    .block (lookupStatement?_sound (node := scopedBlock) rfl) rfl
      (.cons (.expression (lookupStatement?_sound (node := discarded) rfl) rfl first) .nil)
  have ifTrace : Dynamic.StatementExecutes program context [] source sourceEnvironment after (statement 3)
      context (.fallthrough sourceEnvironment) after :=
    .ifFalseWithoutElse (lookupStatement?_sound (node := conditional) rfl) rfl second
  cases mode with
  | false => exact .control (.cons blockTrace (.cons ifTrace
      (.terminal (.returnValue (lookupStatement?_sound (node := finalReturn) rfl) rfl returned) (.returned _))))
  | true => exact .control (.cons blockTrace (.cons ifTrace
      (.singleton (lookupStatement?_sound (node := finalReturn) rfl)
        (by intro expression impossible; cases impossible) (.returnValue (lookupStatement?_sound (node := finalReturn) rfl) rfl returned))))

/-- Actual lowering supplies the entire flow proof in both list modes. -/
theorem accepted_preserves {mode : Bool} {code : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy 12 source scope statements .bool (fun _ => reason) mode reason = .ok code) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (.integer 99 :: administrativeValue :: environment) store (code.rename ξ) value finalStore ∧
      FlowRep (values := values) (registry := values.registry) functions finalMap finalWorld faults .bool .bool (sourceOutcome mode) value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [1] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  exact (Tree.preserves (values := values) functions (.refl _) program [] contextValid unique uninitialized missing
    (certified accepted) initial.2 initial.1 locals agrees actualTyped (sourceTrace mode)).2

/-- Completed generated flow reconstructs the selected independent judgment. -/
theorem accepted_reflects {mode : Bool} {code : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy 12 source scope statements .bool (fun _ => reason) mode reason = .ok code)
    {value : Value} {finalStore : Store}
    (completed : Evaluates (.integer 99 :: administrativeValue :: environment) store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Executes mode program context [] source sourceEnvironment before statements context outcome after ∧
      FlowRep (values := values) (registry := values.registry) functions finalMap finalWorld faults .bool .bool outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [1] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  exact Tree.reflects (values := values) functions (.refl _) program [] contextValid uninitialized missing
    (certified accepted) initial.2 initial.1 locals agrees actualTyped completed

private def rawWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Item { Item(Word) }",
    "function blocks() returns (Bool) { let m: mapping(Bool => Bool); { m[true]; } return !m[false]; }",
    "function absent() returns (Bool) { let m: mapping(Bool => Bool); if (m[true]) { return m[false]; } return !m[false]; }",
    "function nominal() returns (Item) { { } return Item(7); }",
    "function branch(m: mapping(Bool => Bool)) returns (Bool) { if (m[true]) { { m[false]; } if (!m[false]) { return m[true]; } else { return false; } } else { { m[true]; } return !m[false]; } }",
    "function elseFault() returns (Bool) { let m: mapping(Bool => Item); if (false) { return true; } else { { m[true]; } } return false; }",
    "function early() returns (Bool) { let m: mapping(Bool => Item); { return true; } m[true]; return false; }"]}] }

def run : IO Unit := do
  for mode in [false, true] do
    let generated ← SourceCompilerFeatureSupport.get "scoped typed lowering" (compiledResult mode)
    let state : Core.State := ⟨.eval (generated.rename ξ) (.integer 99 :: administrativeValue :: environment), [], store⟩
    let expected : Value := .inLeft LocalLoop.transferType (.inRight .unit (.bool true))
    let complete := Core.runStateful 30000 state
    match Core.LanguageResult.observeResult complete with
    | .succeeded value finalStore =>
        SourceCompilerFeatureSupport.require (value == expected) "recursive scoped control changed return value"
        SourceCompilerFeatureSupport.require (finalStore[0]? == some administrativeValue)
          "scoped index changed the ambient closure cell"
    | _ => throw (IO.userError "actual typed scoped lowering did not complete")
    for fuel in [0, 5, 23] do
      match Core.runStateful fuel state with
      | .outOfFuel suspended =>
          SourceCompilerFeatureSupport.require (Core.runStateful 30000 suspended == complete)
            "resuming the scoped flow changed value or store"
      | _ => throw (IO.userError "scoped flow unexpectedly completed at the suspension prefix")
  let checked ← SourceCompilerFeatureSupport.get "typed scoped checker" (checkProgram rawWorkspace)
  for name in ["blocks", "absent", "early"] do
    let compiled ← SourceCompilerFeatureSupport.compileNamed checked name
    SourceCompilerFeatureSupport.require ((← compiled.run []) == .bool true) "typed scoped branch changed result"
    compiled.checkResume [] (.bool true)
  let branch ← SourceCompilerFeatureSupport.compileNamed checked "branch"
  for input in ([.mapping .bool .bool [],
      .mapping .bool .bool [(.bool true, .bool true)]] : List SourceCoreExecution.Value) do
    SourceCompilerFeatureSupport.require ((← branch.run [input]) == .bool true)
      "nested selected branch changed index captures"
    branch.checkResume [input] (.bool true)
  let failed ← SourceCompilerFeatureSupport.compileNamed checked "elseFault"
  let invocation ← failed.invoke []
  match invocation.outcome with
  | .failed token _ =>
      match ← invocation.diagnostic token with
      | some {error := .typeMismatch _ none, span := some _, ..} => pure ()
      | _ => throw (IO.userError "nested else fault lost raw default diagnostic")
  | _ => throw (IO.userError "nested else missing default did not fail")
  let failedState := SourceCompilerFeatureSupport.sourceState (← failed.audit [])
  match failedState.heap with
  | [cell] =>
      match cell.value with
      | some (.mapping .bool _ []) => pure ()
      | _ => throw (IO.userError "nested else fault lost prior lazy initialization")
  | _ => throw (IO.userError "nested else fault changed source allocation order")
  let nominal ← SourceCompilerFeatureSupport.compileNamed checked "nominal"
  match ← nominal.run [] with
  | .constructed _ [.word value] =>
      SourceCompilerFeatureSupport.require (value == Word.ofNatModulo 7) "empty scoped block changed nominal payload"
  | _ => throw (IO.userError "empty scoped block changed nominal return type")
  IO.println "typed scoped control: block/index/absent-else/return, typed captures, nominal blocks and resume GREEN"
end Tests.SourceCoreTypedScopedControl
end

section
-- leanmerge: from Solcore.Test.SourceCoreTypedScopedStatements
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! The same checked retained expression has two independent list meanings:
function mode returns it; scoped mode discards it and falls through while
retaining a Boolean enclosing type. Actual generated index code also captures
a typed Integer and an ambient closure. No child execution premise is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreTypedScopedStatements
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedScopedStatements
open CompatiblePayload GeneralHeap ReadOnly
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"typed_scoped_statements", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "typed_scoped_statements.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def mappingType : TypeSystem.Ty := .mapping .bool .bool
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "table", .mono mappingType, [], false, none⟩
private def baseNode : ExpressionNode := { id := id 0, span, type := mappingType, form := .reference "table" (.local binder.id) }
private def keyNode : ExpressionNode := { id := id 1, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def indexNode : ExpressionNode := { id := id 2, span, type := .bool, form := .index (id 0) (id 1) }
private def statement (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def discarded : StatementNode := ⟨statement 0, span, .bool, .expression (id 2) false⟩
private def statements := [statement 0]
private def source : TypedSource := {
  owner, inputs := [binder], roots := statements.map .statement,
  nodes := [.expression baseNode, .expression keyNode, .expression indexNode, .statement discarded] }
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem metadata {expression : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp [source] at member
  rcases member with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem boolAdmitted : TypeAdmissible context .bool :=
  .bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme)
private theorem mappingAdmitted : TypeAdmissible context mappingType := .mapping boolAdmitted boolAdmitted
private theorem baseTyped : ExpressionHasType source context (id 0) mappingType := by
  apply ExpressionHasType.ofOrdinary (node := baseNode) (rawType := mappingType) (lookupExpression?_sound (by rfl))
    (.reference (.local (.head) (.head) (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible mappingAdmitted) []
      .empty (by intro metavariable replacement member; cases member) (by exact SchemeInstantiates.empty_apply mappingType)
      (by simp) (by intro _ member; cases member) (.nil)))) mappingAdmitted mappingAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem keyTyped : ExpressionHasType source context (id 1) .bool := by
  apply ExpressionHasType.ofOrdinary (node := keyNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean true)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexTyped : ExpressionHasType source context (id 2) .bool := by
  apply ExpressionHasType.ofOrdinary (node := indexNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.index baseTyped keyTyped) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexSyntax : CompatibleExpressionTyped.Syntax source (id 2) :=
  .index (node := indexNode) (keyNode := keyNode) (by cbv) rfl (by cbv) .bool
    (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.read (node := baseNode) rfl rfl)))))))
    (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := keyNode) rfl (.bool _ _))))))))
private theorem sourceSyntax (mode : Bool) : TypedScopedStatements.Syntax source context mode statements .bool := by
  cases mode with
  | true => exact .tail (node := discarded) (expressionNode := indexNode) rfl rfl rfl rfl rfl indexTyped indexSyntax
  | false =>
      exact .discard (source := source) (context := context) (mode := false)
        (node := discarded) (expressionNode := indexNode) (rest := []) rfl rfl rfl rfl (by cbv)
        indexTyped indexSyntax (.nil (.inl rfl))
private theorem contextValid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal]
  · intro requirement member; cases member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; cases member
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType]).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private theorem nativeExists : (checked.catalog.project mappingType).toOption.isSome = true := by cbv
private def nativeType := (checked.catalog.project mappingType).toOption.get nativeExists
private theorem projected : checked.catalog.project mappingType = .ok nativeType := by cbv
private def scope : SourceCoreLocalCell.Scope := [(binder.id, nativeType)]
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source scope context := by
  intro actual declared index native selected accepted
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst actual
    have actual : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder := by rfl
    rw [actual] at accepted
    cases accepted
    exact .head
  · simp at selected
private abbrev expressionPolicy := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
private def policy : SourceCoreLoops.Policy := {
  lowerExpression := fun fuel source scope expression reasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody fuel compilation source scope expression reasonAt
  readStatement := SourceCoreCompatibleDataExpressions.readStatement checked }
private theorem certified {mode : Bool} {code : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy 12 source scope statements .bool (fun _ => reason) mode reason = .ok code) :
    Tree 100 values source context [] (fun _ => reason) scope mode statements .bool .bool code := by
  apply tree_of_flow rfl ?_ (sourceSyntax mode) rfl accepted
  intro budget expression node lowered childSyntax found typed generated
  exact CompatibleExpressionTyped.tree_of_functions unique declarations rfl rfl rfl
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ (fun _ _ _ found => (metadata found).2)
    childSyntax found typed generated

private def compiledResult (mode : Bool) := SourceCoreLoops.lowerFlowStatementsWithPolicy policy 12 source scope statements
  .bool (fun _ => reason) mode reason
private def frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [frameLayout.definition]
private def functions : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def model := CompatibleAmbientHeap.payloadModel checked values.registry functions
private def faults : FunctionCalls.FaultRep := fun error token =>
  ((∃ location, error = .uninitializedLocation location) ∧ token = reason) ∨
  (∃ key value tag, MetadataRep values.registry (.mapping key value) tag ∧ error = .missingMappingDefault value ∧ token = reason.add tag)
private theorem uninitialized : ∀ (id : ExpressionId) location, faults (.uninitializedLocation location) ((fun _ => reason) id) :=
  fun _ location => .inl ⟨⟨location, rfl⟩, rfl⟩
private theorem missing : ∀ (id : ExpressionId) key value tag, MetadataRep values.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) (((fun _ => reason) id).add tag) :=
  fun _ key value tag owned => .inr ⟨key, value, tag, owned, rfl, rfl⟩
private def administrativeType : Ty := .function .unit frameLayout.type
private def administrativeValue : Value := .closure .unit frameLayout.type (.var 1) [SourceCoreCallableIndexedFrames.encode frameLayout .empty]
private theorem frameRegistered : frameLayout.Registered ambient.definitions := by
  constructor
  simp [ambient, AmbientDefinitions.append, frameLayout]
private theorem administrativeTyped : RuntimeValueHasType [] administrativeValue administrativeType ambient.definitions :=
  .closure (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed [] frameRegistered .empty) .nil) (.var rfl)
private def world : StoreTyping := [administrativeType, OptionalCell.cellType nativeType]
private def store : Store := [administrativeValue, .inLeft nativeType .unit]
private def environment : Environment := [.cellRef (OptionalCell.cellType nativeType) 1]
private def sourceEnvironment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def before : Dynamic.Heap := ⟨[⟨mappingType, none, none⟩]⟩
private def after : Dynamic.Heap := ⟨[⟨mappingType, some (.mapping .bool .bool []), none⟩]⟩
private theorem initial : GenericHeap.HeapRepresents model [1] world before store ∧
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) [1] world [] scope sourceEnvironment environment ambient.definitions := by
  have empty := (GenericHeap.HeapRepresents.empty (model := model)).allocate_administrative administrativeTyped
  obtain ⟨heap, reference⟩ := empty.allocate (.uninitialized projected) Dynamic.Heap.Allocates.append
  exact ⟨heap, .cons reference (.nil .nil)⟩
private theorem locals : Dynamic.EnvironmentAgrees before context.locals sourceEnvironment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem actualTyped : RuntimeEnvironmentHasTypes world (.integer 99 :: administrativeValue :: environment)
    [.integer, administrativeType, .cell (OptionalCell.cellType nativeType)] ambient.definitions :=
  .cons .integer (.cons (administrativeTyped.weaken ⟨world, rfl⟩) (.cons (.cellRef rfl) .nil))
private def ξ : Renaming := Renaming.comp (Renaming.insertion 0) (Renaming.insertion 0)
private theorem agrees : EnvironmentsAgree ξ environment (.integer 99 :: administrativeValue :: environment) :=
  GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix (show EnvironmentsAgree Renaming.id environment environment from fun {_ _} found => found) administrativeValue) (.integer 99)
private theorem initialRead : Dynamic.ExpressionEvaluatesOutcome program context [] source sourceEnvironment before (id 2) (.value (.bool false)) after := by
  apply Dynamic.ExpressionEvaluatesOutcome.value
  apply Dynamic.ExpressionEvaluates.intro (raw := .bool false) (middle := after) (lookupExpression?_sound (node := indexNode) (by cbv))
  · change Dynamic.ExpressionFormEvaluates program context [] source sourceEnvironment before (.index (id 0) (id 1)) [] [] (.bool false) after
    apply Dynamic.ExpressionFormEvaluates.indexDefault (coercions := []) rfl
    · exact .intro (lookupExpression?_sound (node := baseNode) (by rfl))
        (.localEmptyMapping rfl .head (.intro .head) rfl rfl rfl (.intro (.intro .head) .head)) .nil
    · exact .intro (lookupExpression?_sound (node := keyNode) (by cbv)) (.builtinBoolean rfl) .nil
    · exact .nil
    · exact .bool
  · exact .nil

private def sourceOutcome (mode : Bool) : Dynamic.ControlOutcome :=
  if mode then .returned (.bool false) else .fallthrough sourceEnvironment
private theorem sourceTrace (mode : Bool) : Executes mode program context [] source sourceEnvironment before
    statements context (sourceOutcome mode) after := by
  have first : Dynamic.ExpressionEvaluates program context [] source sourceEnvironment before (id 2) (.bool false) after := by
    cases initialRead with | value evaluated => exact evaluated
  cases mode with
  | true => exact .control (.tailExpression (lookupStatement?_sound (node := discarded) rfl) rfl first)
  | false => exact .control (.cons (.expression (lookupStatement?_sound (node := discarded) rfl) rfl first) .nil)

/-- Actual lowering supplies the entire flow proof in both list modes. -/
theorem accepted_preserves {mode : Bool} {code : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy 12 source scope statements .bool (fun _ => reason) mode reason = .ok code) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (.integer 99 :: administrativeValue :: environment) store (code.rename ξ) value finalStore ∧
      FlowRep (values := values) (registry := values.registry) functions finalMap finalWorld faults .bool .bool (sourceOutcome mode) value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [1] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  exact (Tree.preserves (values := values) functions (.refl _) program [] contextValid unique uninitialized missing
    (certified accepted) initial.2 initial.1 locals agrees actualTyped (sourceTrace mode)).2

/-- Completed generated flow reconstructs the selected independent judgment. -/
theorem accepted_reflects {mode : Bool} {code : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy 12 source scope statements .bool (fun _ => reason) mode reason = .ok code)
    {value : Value} {finalStore : Store}
    (completed : Evaluates (.integer 99 :: administrativeValue :: environment) store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Executes mode program context [] source sourceEnvironment before statements context outcome after ∧
      FlowRep (values := values) (registry := values.registry) functions finalMap finalWorld faults .bool .bool outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [1] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  exact Tree.reflects (values := values) functions (.refl _) program [] contextValid uninitialized missing
    (certified accepted) initial.2 initial.1 locals agrees actualTyped completed

private theorem scoped_bool_nil (code : Expr)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy 0 source scope [] .bool (fun _ => reason) false reason = .ok code) :
    Tree 100 values source context [] (fun _ => reason) scope false [] .bool .bool code :=
  tree_of_flow rfl (by
    intro budget expression node lowered childSyntax found typed generated
    exact CompatibleExpressionTyped.tree_of_functions unique declarations rfl rfl rfl
      ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ (fun _ _ _ found => (metadata found).2)
      childSyntax found typed generated) (.nil (.inl rfl)) rfl accepted

private def rawWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Item { Item(Word) }",
    "function blocks() returns (Bool) { let m: mapping(Bool => Bool); { m[true]; } return !m[false]; }",
    "function absent() returns (Bool) { let m: mapping(Bool => Bool); if (m[true]) { return m[false]; } return !m[false]; }",
    "function nominal() returns (Item) { { } return Item(7); }",
    "function early() returns (Bool) { let m: mapping(Bool => Item); { return true; } m[true]; return false; }"]}] }

def run : IO Unit := do
  for mode in [false, true] do
    let generated ← SourceCompilerFeatureSupport.get "scoped typed lowering" (compiledResult mode)
    let state : Core.State := ⟨.eval (generated.rename ξ) (.integer 99 :: administrativeValue :: environment), [], store⟩
    let expected : Value := if mode then .inLeft LocalLoop.transferType (.inRight .unit (.bool false))
      else .inLeft LocalLoop.transferType (.inLeft .bool .unit)
    let complete := Core.runStateful 30000 state
    match Core.LanguageResult.observeResult complete with
    | .succeeded value finalStore =>
        SourceCompilerFeatureSupport.require (value == expected) "function/scoped tail expression changed control mode"
        SourceCompilerFeatureSupport.require (finalStore[0]? == some administrativeValue)
          "scoped index changed the ambient closure cell"
    | _ => throw (IO.userError "actual typed scoped lowering did not complete")
    for fuel in [0, 5, 23] do
      match Core.runStateful fuel state with
      | .outOfFuel suspended =>
          SourceCompilerFeatureSupport.require (Core.runStateful 30000 suspended == complete)
            "resuming the scoped flow changed value or store"
      | _ => throw (IO.userError "scoped flow unexpectedly completed at the suspension prefix")
  let checked ← SourceCompilerFeatureSupport.get "typed scoped checker" (checkProgram rawWorkspace)
  for name in ["blocks", "absent", "early"] do
    let compiled ← SourceCompilerFeatureSupport.compileNamed checked name
    SourceCompilerFeatureSupport.require ((← compiled.run []) == .bool true) "typed scoped branch changed result"
    compiled.checkResume [] (.bool true)
  let nominal ← SourceCompilerFeatureSupport.compileNamed checked "nominal"
  match ← nominal.run [] with
  | .constructed _ [.word value] =>
      SourceCompilerFeatureSupport.require (value == Word.ofNatModulo 7) "empty scoped block changed nominal payload"
  | _ => throw (IO.userError "empty scoped block changed nominal return type")
  IO.println "typed scoped statements: both tail modes, Bool fallthrough, ambient captures, nominal blocks and resume GREEN"
end Tests.SourceCoreTypedScopedStatements
end

section
-- leanmerge: from Solcore.Test.SourceCoreTypedStatementMixed
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Typed mapping initializers reach three source allocations, then fail in the fourth
binding's initializer. Lazy initialization, static receipts and independent semantics agree on the exact
intermediate lexical context; real cached calls exercise longer prefixes. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreTypedStatementMixed
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedStatementMixed CompatiblePayload GeneralHeap ReadOnly CallableIndexedHistory
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"typed_mixed_binding", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "typed_mixed.solc"⟩, 0, 1⟩
private def expression (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def binder (index : Nat) : TypedBinder := ⟨⟨owner, index⟩, "value", .mono .bool, [], false, none⟩
private def mappingType : TypeSystem.Ty := .mapping .bool .bool
private def inputBinder : TypedBinder := ⟨⟨owner, 0⟩, "input", .mono mappingType, [], false, none⟩
private def inputNode : ExpressionNode := {id := expression 0, span, type := mappingType, form := .reference "input" (.local inputBinder.id)}
private def keyNode : ExpressionNode := {id := expression 2, span, type := .bool, form := .reference "true" (.builtinBoolean true)}
private def indexNode : ExpressionNode := {id := expression 3, span, type := .bool, form := .index (expression 0) (expression 2)}
private def missingNode : ExpressionNode := {id := expression 1, span, type := .bool, form := .reference "missing" (.local (binder 2).id)}
private def first : StatementNode := ⟨statement 0, span, .unit, .letDecl (binder 1) (some (expression 3))⟩
private def second : StatementNode := ⟨statement 1, span, .unit, .letDecl (binder 2) none⟩
private def third : StatementNode := ⟨statement 2, span, .unit, .letDecl (binder 3) (some (expression 3))⟩
private def fourth : StatementNode := ⟨statement 3, span, .unit, .letDecl (binder 4) (some (expression 1))⟩
private def returned : StatementNode := ⟨statement 4, span, .unit, .returnStmt none⟩
private def statements := [statement 0, statement 1, statement 2, statement 3, statement 4]
private def source : TypedSource := {
  owner, inputs := [inputBinder], roots := statements.map .statement,
  nodes := [.expression inputNode, .expression missingNode, .expression keyNode, .expression indexNode, .statement first, .statement second,
    .statement third, .statement fourth, .statement returned] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def initial : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal inputBinder.id inputBinder.scheme
private def context1 := initial.withLocal (binder 1).id (binder 1).scheme
private def context2 := context1.withLocal (binder 2).id (binder 2).scheme
private def context3 := context2.withLocal (binder 3).id (binder 3).scheme
private def context4 := context3.withLocal (binder 4).id (binder 4).scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def reason := Word.ofNatModulo 37
private theorem extend {context : SourceSemantics.Context} (index : Nat)
    (binders : TypeParameterBindersWellFormed context) (fresh : LocalFresh context (binder index).id) :
    BinderExtends owner context (binder index) (context.withLocal (binder index).id (binder index).scheme) := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {binders, quantified_nodup := by simp [binder, TypeSystem.Scheme.mono], body := .builtin .bool}
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl }
  · exact fresh
private theorem extension1 : BinderExtends owner initial (binder 1) context1 := by
  apply extend 1
  · simp [TypeParameterBindersWellFormed, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, signatures]
  · simp [LocalFresh, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder, inputBinder]
private theorem extension2 : BinderExtends owner context1 (binder 2) context2 := by
  apply extend 2
  · simp [TypeParameterBindersWellFormed, context1, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, signatures]
  · simp [LocalFresh, context1, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder, inputBinder]
private theorem extension3 : BinderExtends owner context2 (binder 3) context3 := by
  apply extend 3
  · simp [TypeParameterBindersWellFormed, context1, context2, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, signatures]
  · simp [LocalFresh, context1, context2, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder, inputBinder]
private theorem extension4 : BinderExtends owner context3 (binder 4) context4 := by
  apply extend 4
  · simp [TypeParameterBindersWellFormed, context1, context2, context3, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, signatures]
  · simp [LocalFresh, context1, context2, context3, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder, inputBinder]
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem localTyped {context : SourceSemantics.Context} {node : ExpressionNode} {index : Nat}
    (found : source.lookupExpression? node.id = some node)
    (form : node.form = .reference "input" (.local (binder index).id) ∨ node.form = .reference "missing" (.local (binder index).id))
    (type : node.type = .bool) (requirements : node.requirements = []) (coercions : node.coercions = [])
    (binders : TypeParameterBindersWellFormed context)
    (lookup : Resolved.LocalScope.Lookup context.locals (binder index).id (binder index).scheme)
    (schemes : context.LocalSchemeRequirementsLookup (binder index).id []) :
    ExpressionHasType source context node.id node.type := by
  have admitted : TypeAdmissible context .bool := .bool binders
  rcases form with form | form
  all_goals
    apply ExpressionHasType.ofOrdinary (rawType := .bool) (owned := []) (lookupExpression?_sound found)
    · rw [form]
      exact .reference (.local lookup schemes (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible admitted) []
        .empty (by intro metavariable replacement member; cases member) (SchemeInstantiates.empty_apply _)
        (by simp) (by intro _ member; cases member) .nil))
    · exact admitted
    · exact type ▸ admitted
    · intro requirement member; cases member
    · rw [coercions, type]; exact .nil _
    · simp [requirements, coercions, coercionRequirementIds]
private theorem inputTyped {context : SourceSemantics.Context}
    (binders : TypeParameterBindersWellFormed context)
    (lookup : Resolved.LocalScope.Lookup context.locals inputBinder.id inputBinder.scheme)
    (schemes : context.LocalSchemeRequirementsLookup inputBinder.id []) :
    ExpressionHasType source context (expression 0) mappingType := by
  have admitted : TypeAdmissible context mappingType := .mapping (.bool binders) (.bool binders)
  apply ExpressionHasType.ofOrdinary (node := inputNode) (rawType := mappingType) (lookupExpression?_sound rfl)
    (.reference (.local lookup schemes (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible admitted) []
      .empty (by intro metavariable replacement member; cases member) (SchemeInstantiates.empty_apply _)
      (by simp) (by intro _ member; cases member) .nil))) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexTyped {context : SourceSemantics.Context}
    (binders : TypeParameterBindersWellFormed context)
    (lookup : Resolved.LocalScope.Lookup context.locals inputBinder.id inputBinder.scheme)
    (schemes : context.LocalSchemeRequirementsLookup inputBinder.id []) :
    ExpressionHasType source context (expression 3) .bool := by
  have admitted : TypeAdmissible context .bool := .bool binders
  have key : ExpressionHasType source context (expression 2) .bool := by
    apply ExpressionHasType.ofOrdinary (node := keyNode) (rawType := .bool) (lookupExpression?_sound rfl)
      (.reference (.builtinBoolean true)) admitted admitted
    · intro requirement member; cases member
    · exact .nil _
    · rfl
  apply ExpressionHasType.ofOrdinary (node := indexNode) (rawType := .bool) (lookupExpression?_sound rfl)
    (.index (inputTyped binders lookup schemes) key) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem inputInitial : ExpressionHasType source initial (expression 3) .bool :=
  indexTyped ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _) .head .head
private theorem inputSecond : ExpressionHasType source context2 (expression 3) .bool :=
  indexTyped ((((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _).withLocal _ _).withLocal _ _)
    (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
private theorem missingThird : ExpressionHasType source context3 (expression 1) .bool := by
  apply localTyped (node := missingNode) (index := 2) rfl (.inr rfl) rfl rfl rfl
  · exact ((((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _).withLocal _ _).withLocal _ _).withLocal _ _
  · exact .tail (by decide) .head
  · exact .tail (by decide) .head
private theorem inputSyntax : CompatibleExpressionTyped.Syntax source (expression 3) :=
  .index (node := indexNode) (keyNode := keyNode) rfl rfl rfl .bool
    (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.read (node := inputNode) rfl rfl)))))))
    (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := keyNode) rfl (.bool _ _))))))))
private theorem missingSyntax : CompatibleExpressionTyped.Syntax source (expression 1) :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.read (node := missingNode) rfl rfl))))))
private theorem syntaxTree : Syntax source initial statements .unit :=
  .initialized (node := first) (initializerNode := indexNode) rfl rfl rfl rfl extension1 (by decide)
    rfl rfl inputInitial inputSyntax
    (.uninitialized (node := second) rfl rfl rfl rfl extension2 (by decide)
      (.initialized (node := third) (initializerNode := indexNode) rfl rfl rfl rfl extension3 (by decide)
        rfl rfl inputSecond inputSyntax
        (.initialized (node := fourth) (initializerNode := missingNode) rfl rfl rfl rfl extension4 (by decide)
          rfl rfl missingThird missingSyntax (.body (.returnUnit (node := returned) [] rfl rfl rfl)))))
private theorem valid : CompatibleExpressionLiterals.ContextValid [] initial [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal]
  · intro requirement member
    simp [initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member
      simp [initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
private theorem prepared : (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType, .bool, .unit]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType, .bool, .unit]).toOption.get prepared
private def values := SourceCoreCompatibleValues.Context.initial checked
private theorem nativeExists : (checked.catalog.project mappingType).toOption.isSome = true := by cbv
private def nativeType := (checked.catalog.project mappingType).toOption.get nativeExists
private def scope : SourceCoreLocalCell.Scope := [(inputBinder.id, nativeType)]
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def expressionPolicy := SourceCoreCompatibleDataExpressions.functionPolicy 10 values
private def onError (_ : SourceCoreAllocationLayouts.Error) : SourceCoreBasic.Error := .traversalExhausted (.declaration owner)
private def policy (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) : SourceCoreLoops.Policy := {
  lowerExpression := fun fuel source scope id reasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody fuel compilation source scope id reasonAt
  readStatement := SourceCoreCompatibleDataExpressions.readStatement checked
  lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder checked
  sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt ⟨owner, []⟩ [] onError)) }
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source scope initial := by
  intro id declared index type selected authentic
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst id
    have found : SourceCoreDataPlaces.rootBinder source inputBinder.id = .ok inputBinder := rfl
    rw [found] at authentic; cases authentic
    exact .head
  · simp at selected
private theorem metadata {id : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp [source] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

private theorem certified {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) fuel source scope
      statements .unit (fun _ => reason) reason reason = .ok code) :
    ∃ flow, code = CompatibleStatements.finish .unit flow reason reason ∧
      Tree layouts ⟨owner, []⟩ [] frame globals onError 10 values source [] (fun _ => reason)
        initial scope statements .unit .unit flow := by
  apply tree_of_body rfl (fun _ _ _ => rfl) rfl ?_ syntaxTree rfl rfl rfl declarations rfl accepted
  intro current closed residual sameSignatures currentScope budget id node lowered declared childSyntax found typed generated
  exact CompatibleExpressionTyped.tree_of_functions unique declared sameSignatures closed residual
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ (fun _ _ _ found => metadata found)
    childSyntax found typed generated

private def sourceEnvironment : Dynamic.Environment := [(inputBinder.id, ⟨0⟩)]
private def environment1 : Dynamic.Environment := ((binder 1).id, ⟨1⟩) :: sourceEnvironment
private def environment2 : Dynamic.Environment := ((binder 2).id, ⟨2⟩) :: environment1
private def environment3 : Dynamic.Environment := ((binder 3).id, ⟨3⟩) :: environment2
private def sourceHeap : Dynamic.Heap := ⟨[⟨mappingType, none, none⟩]⟩
private def initializedHeap : Dynamic.Heap := ⟨[⟨mappingType, some (.mapping .bool .bool []), none⟩]⟩
private def heap1 : Dynamic.Heap := ⟨initializedHeap.cells ++ [⟨.bool, some (.bool false), none⟩]⟩
private def heap2 : Dynamic.Heap := ⟨heap1.cells ++ [⟨.bool, none, none⟩]⟩
private def heap3 : Dynamic.Heap := ⟨heap2.cells ++ [⟨.bool, some (.bool false), none⟩]⟩
private theorem firstIndex : Dynamic.ExpressionEvaluates program initial [] source sourceEnvironment sourceHeap
    (expression 3) (.bool false) initializedHeap := by
  apply Dynamic.ExpressionEvaluates.intro (node := indexNode) (raw := .bool false) (middle := initializedHeap) (lookupExpression?_sound rfl)
  · apply Dynamic.ExpressionFormEvaluates.indexDefault (coercions := []) rfl
    · exact .intro (node := inputNode) (lookupExpression?_sound rfl)
        (.localEmptyMapping rfl .head (.intro .head) rfl rfl rfl (.intro (.intro .head) .head)) .nil
    · exact .intro (node := keyNode) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil
    · exact .nil
    · exact .bool
  · exact .nil
private theorem thirdIndex : Dynamic.ExpressionEvaluates program context2 [] source environment2 heap2
    (expression 3) (.bool false) heap2 := by
  apply Dynamic.ExpressionEvaluates.intro (node := indexNode) (raw := .bool false) (middle := heap2) (lookupExpression?_sound rfl)
  · apply Dynamic.ExpressionFormEvaluates.indexDefault (coercions := []) rfl
    · exact .intro (node := inputNode) (lookupExpression?_sound rfl)
        (.local rfl (.tail (by decide) (.tail (by decide) .head)) (.intro .head) rfl rfl) .nil
    · exact .intro (node := keyNode) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil
    · exact .nil
    · exact .bool
  · exact .nil
private theorem sourceFailure : Dynamic.FunctionStatementsExecuteOutcome program initial [] source sourceEnvironment sourceHeap
    statements context3 (.fault (.uninitializedLocation ⟨2⟩)) heap3 := by
  apply Dynamic.FunctionStatementsExecuteOutcome.fault
  apply Dynamic.FunctionStatementsFault.tail
    (Dynamic.StatementExecutes.letInitialized (node := first) (lookupStatement?_sound rfl) rfl firstIndex
      rfl extension1 .append)
  apply Dynamic.FunctionStatementsFault.tail
    (Dynamic.StatementExecutes.letUninitialized (node := second) (lookupStatement?_sound rfl) rfl rfl extension2 .append)
  apply Dynamic.FunctionStatementsFault.tail
    (Dynamic.StatementExecutes.letInitialized (node := third) (lookupStatement?_sound rfl) rfl thirdIndex
      rfl extension3 .append)
  apply Dynamic.FunctionStatementsFault.head
  apply Dynamic.StatementFaults.letInitializer (node := fourth) (lookupStatement?_sound rfl) rfl rfl
  apply Dynamic.ExpressionFaults.form (node := missingNode) (lookupExpression?_sound rfl)
  exact .localUninitialized (owned := []) (coercions := []) (cell := ⟨.bool, none, none⟩)
    rfl (.tail (by decide) .head) (.intro (.tail (.tail .head))) rfl rfl
      (by rintro ⟨key, value, impossible⟩; cases impossible)

private def faults : FunctionCalls.FaultRep := fun error token =>
  ((∃ location, error = .uninitializedLocation location) ∧ token = reason) ∨
  (∃ key value tag, MetadataRep values.registry (.mapping key value) tag ∧ error = .missingMappingDefault value ∧ token = reason.add tag)
private theorem uninitialized : ∀ (id : ExpressionId) location, faults (.uninitializedLocation location) ((fun _ => reason) id) :=
  fun _ location => .inl ⟨⟨location, rfl⟩, rfl⟩
private theorem missing : ∀ (id : ExpressionId) key value tag, MetadataRep values.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) (((fun _ => reason) id).add tag) :=
  fun _ key value tag owned => .inr ⟨key, value, tag, owned, rfl, rfl⟩

private theorem failureContext_ne_full : context3 ≠ context4 := by
  intro same
  have impossible : 4 = 5 := congrArg (fun context => context.locals.length) same
  omega

/-- Three successful bindings precede the fault. Reflection recovers that
intermediate context and represented lexical environment from actual code. -/
theorem compiled_reflects {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) fuel source scope
      statements .unit (fun _ => reason) reason reason = .ok code)
    {mapping world administrative actualContext canonical actual heap store ξ contextLocation native value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap initial.locals sourceEnvironment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program initial [] source sourceEnvironment heap
        statements resultContext outcome after ∧
      CompatibleStatements.BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld
        faults .unit .unit outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      LexicalResult checked ambient.definitions finalMap finalWorld administrative source.owner
        initial scope sourceEnvironment resultContext after := by
  obtain ⟨flow, rfl, tree⟩ := certified accepted
  exact Tree.body_reflects (values := values) (ambient := ambient) (faults := faults)
    functions definitions registered (.refl _) program [] uninitialized missing
    tree valid reason reason environments heaps locals agrees typed reference read unmapped completed

theorem compiled_failure_preserves {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) fuel source scope
      statements .unit (fun _ => reason) reason reason = .ok code)
    {mapping world administrative actualContext canonical actual store ξ contextLocation native}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world sourceHeap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      CompatibleStatements.BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld
        faults .unit .unit (.fault (.uninitializedLocation ⟨2⟩)) value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld heap3 finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend sourceHeap heap3 ∧
      LexicalResult checked ambient.definitions finalMap finalWorld administrative source.owner
        initial scope sourceEnvironment context3 heap3 := by
  obtain ⟨flow, rfl, tree⟩ := certified accepted
  exact Tree.body_preserves (values := values) (ambient := ambient) (faults := faults)
    functions definitions registered (.refl _) program [] uninitialized missing
    tree valid reason reason unique environments heaps (.cons (.intro .head) rfl (.ordinary rfl rfl) .nil)
    agrees typed reference read unmapped sourceFailure

private def rawWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Bool) }",
    "function mixed() returns (Bool) { let m: mapping(Bool => Bool); let a = m[true]; let unused: Word; let b = !m[false]; let c: Bool; let d = a ? m[false] : b; m[true]; return d; }",
    "function fail() returns (Bool) { let m: mapping(Bool => Bool); let a = m[true]; let missing: Bool; let c = m[false]; let d = (m[true], missing); let never = false; return a; }",
    "function missingDefault() returns (Bool) { let m: mapping(Bool => Box); let a = true; let gap: Word; let failed = m[true]; let never = false; return a; }",
    "function boxed() returns (Box) { let m: mapping(Bool => Bool); let a: Box = .Box(!m[true]); let missing: Bool; let b = a; let c = b; return c; }"]}] }

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "typed mixed checker" (checkProgram rawWorkspace)
  let mixed ← SourceCompilerFeatureSupport.compileNamed checked "mixed"
  SourceCompilerFeatureSupport.require ((← mixed.run []) == .bool true) "typed mixed result changed"
  mixed.checkCells [] [(.mapping .bool .bool, some (.mapping .bool .bool [])), (.bool, some (.bool false)),
    (.word, none), (.bool, some (.bool true)), (.bool, none), (.bool, some (.bool true))]
  mixed.checkResume [] (.bool true)
  let fail ← SourceCompilerFeatureSupport.compileNamed checked "fail"
  let invocation ← fail.invoke []
  match invocation.outcome with
  | .failed token complete =>
      SourceCompilerFeatureSupport.require (← invocation.diagnostic token).isSome "typed mixed fault diagnostic missing"
      let suspended ← SourceCompilerFeatureSupport.get "typed mixed suspension"
        (← invocation.initial.run invocation.key [] {SourceCompilerFeatureSupport.executionOptions with executionFuel := 10})
      let checkpoint ← match suspended with
        | .outOfFuel checkpoint => pure checkpoint
        | _ => throw (IO.userError "typed mixed fixture did not suspend")
      match ← checkpoint.resume 300000 1024 with
      | .failed resumed finished =>
          SourceCompilerFeatureSupport.require (resumed == token && finished.heapSize == complete.heapSize)
            "resumption changed failure or allocated an unreachable binding"
      | _ => throw (IO.userError "typed mixed checkpoint changed outcome")
  | _ => throw (IO.userError "absent typed initializer did not fail")
  fail.checkCells [] [(.mapping .bool .bool, some (.mapping .bool .bool [])),
    (.bool, some (.bool false)), (.bool, none), (.bool, some (.bool false))]
  let missingDefault ← SourceCompilerFeatureSupport.compileNamed checked "missingDefault"
  let invocation ← missingDefault.invoke []
  match invocation.outcome with
  | .failed token _ =>
      match ← invocation.diagnostic token with
      | some {error := .typeMismatch _ none, span := some _, ..} => pure ()
      | _ => throw (IO.userError "initializer missing-default diagnostic lost raw metadata/span")
  | _ => throw (IO.userError "nominal missing-default initializer did not fail")
  let cells := (SourceCompilerFeatureSupport.sourceState (← missingDefault.audit [])).heap
  match cells with
  | [mapping, first, gap] =>
      SourceCompilerFeatureSupport.require ((match first.value with | some (.bool true) => true | _ => false) && gap.type == .word && gap.value.isNone)
        "initializer fault changed preceding allocation order"
      match mapping.value with
      | some (.mapping .bool _ []) => pure ()
      | _ => throw (IO.userError "initializer fault lost lazy root initialization")
  | _ => throw (IO.userError "failed initializer allocated a source binder or continuation")
  let boxed ← SourceCompilerFeatureSupport.compileNamed checked "boxed"
  match ← boxed.run [] with
  | .constructed _ [.bool true] => pure ()
  | _ => throw (IO.userError "typed mixed nominal/index initializer changed")
  IO.println "typed mixed statements: marked allocation, index initializers, intermediate context, lazy effects, failure suppression and resume GREEN"
end Tests.SourceCoreTypedStatementMixed
end

section
-- leanmerge: from Solcore.Test.SourceCoreTypedStatements
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Repeated indexing crosses a discarded-payload slot and captures a real
ambient closure. The full source statement trace and completed reflection
consume actual lowering receipts, without a child/body semantic premise. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreTypedStatements
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedStatements
open CompatibleStatements (FlowRep BodyRep)
open CompatiblePayload GeneralHeap ReadOnly
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"typed_statements", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "typed_statements.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def mappingType : TypeSystem.Ty := .mapping .bool .bool
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "table", .mono mappingType, [], false, none⟩
private def baseNode : ExpressionNode := { id := id 0, span, type := mappingType, form := .reference "table" (.local binder.id) }
private def keyNode : ExpressionNode := { id := id 1, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def indexNode : ExpressionNode := { id := id 2, span, type := .bool, form := .index (id 0) (id 1) }
private def statement (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def discarded : StatementNode := ⟨statement 0, span, .unit, .expression (id 2) true⟩
private def returned : StatementNode := ⟨statement 1, span, .bool, .returnStmt (some (id 2))⟩
private def unreachable : StatementNode := ⟨statement 2, span, .unit, .breakStmt⟩
private def statements := [statement 0, statement 1, statement 2]
private def source : TypedSource := {
  owner, inputs := [binder], roots := statements.map .statement,
  nodes := [.expression baseNode, .expression keyNode, .expression indexNode,
    .statement discarded, .statement returned, .statement unreachable] }
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem metadata {expression : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp [source] at member
  rcases member with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem boolAdmitted : TypeAdmissible context .bool :=
  .bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme)
private theorem mappingAdmitted : TypeAdmissible context mappingType := .mapping boolAdmitted boolAdmitted
private theorem baseTyped : ExpressionHasType source context (id 0) mappingType := by
  apply ExpressionHasType.ofOrdinary (node := baseNode) (rawType := mappingType) (lookupExpression?_sound (by rfl))
    (.reference (.local (.head) (.head) (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible mappingAdmitted) []
      .empty (by intro metavariable replacement member; cases member) (by exact SchemeInstantiates.empty_apply mappingType)
      (by simp) (by intro _ member; cases member) (.nil)))) mappingAdmitted mappingAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem keyTyped : ExpressionHasType source context (id 1) .bool := by
  apply ExpressionHasType.ofOrdinary (node := keyNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean true)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexTyped : ExpressionHasType source context (id 2) .bool := by
  apply ExpressionHasType.ofOrdinary (node := indexNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.index baseTyped keyTyped) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexSyntax : CompatibleExpressionTyped.Syntax source (id 2) :=
  .index (node := indexNode) (keyNode := keyNode) (by cbv) rfl (by cbv) .bool
    (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.read (node := baseNode) rfl rfl)))))))
    (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := keyNode) rfl (.bool _ _))))))))
private theorem sourceSyntax : TypedStatements.Syntax source context statements .bool :=
  .discard (node := discarded) (expressionNode := indexNode) rfl rfl rfl rfl rfl indexTyped indexSyntax
    (.returnValue (node := returned) (expressionNode := indexNode) [statement 2] rfl rfl rfl rfl rfl indexTyped indexSyntax)
private theorem contextValid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal]
  · intro requirement member; cases member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; cases member
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType]).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private theorem nativeExists : (checked.catalog.project mappingType).toOption.isSome = true := by cbv
private def nativeType := (checked.catalog.project mappingType).toOption.get nativeExists
private theorem projected : checked.catalog.project mappingType = .ok nativeType := by cbv
private def scope : SourceCoreLocalCell.Scope := [(binder.id, nativeType)]
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source scope context := by
  intro actual declared index native selected accepted
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst actual
    have actual : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder := by rfl
    rw [actual] at accepted
    cases accepted
    exact .head
  · simp at selected
private abbrev expressionPolicy := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
private def policy : SourceCoreLoops.Policy := {
  lowerExpression := fun fuel source scope expression reasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody fuel compilation source scope expression reasonAt
  readStatement := SourceCoreCompatibleDataExpressions.readStatement checked }
private theorem certified {code : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy 12 source scope statements .bool (fun _ => reason) reason reason = .ok code) :
    ∃ flow, code = finish .bool flow reason reason ∧ Tree 100 values source context [] (fun _ => reason) scope statements .bool .bool flow := by
  apply tree_of_body rfl ?_ sourceSyntax rfl accepted
  intro budget expression node lowered childSyntax found typed generated
  exact CompatibleExpressionTyped.tree_of_functions unique declarations rfl rfl rfl
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ (fun _ _ _ found => (metadata found).2)
    childSyntax found typed generated

private def compiledResult := SourceCoreLoops.lowerStatementsWithPolicy policy 12 source scope statements
  .bool (fun _ => reason) reason reason
private def frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [frameLayout.definition]
private def functions : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def model := CompatibleAmbientHeap.payloadModel checked values.registry functions
private def faults : FunctionCalls.FaultRep := fun error token =>
  ((∃ location, error = .uninitializedLocation location) ∧ token = reason) ∨
  (∃ key value tag, MetadataRep values.registry (.mapping key value) tag ∧ error = .missingMappingDefault value ∧ token = reason.add tag)
private theorem uninitialized : ∀ (id : ExpressionId) location, faults (.uninitializedLocation location) ((fun _ => reason) id) :=
  fun _ location => .inl ⟨⟨location, rfl⟩, rfl⟩
private theorem missing : ∀ (id : ExpressionId) key value tag, MetadataRep values.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) (((fun _ => reason) id).add tag) :=
  fun _ key value tag owned => .inr ⟨key, value, tag, owned, rfl, rfl⟩
private def administrativeType : Ty := .function .unit frameLayout.type
private def administrativeValue : Value := .closure .unit frameLayout.type (.var 1) [SourceCoreCallableIndexedFrames.encode frameLayout .empty]
private theorem frameRegistered : frameLayout.Registered ambient.definitions := by
  constructor
  simp [ambient, AmbientDefinitions.append, frameLayout]
private theorem administrativeTyped : RuntimeValueHasType [] administrativeValue administrativeType ambient.definitions :=
  .closure (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed [] frameRegistered .empty) .nil) (.var rfl)
private def world : StoreTyping := [administrativeType, OptionalCell.cellType nativeType]
private def store : Store := [administrativeValue, .inLeft nativeType .unit]
private def environment : Environment := [.cellRef (OptionalCell.cellType nativeType) 1]
private def sourceEnvironment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def before : Dynamic.Heap := ⟨[⟨mappingType, none, none⟩]⟩
private def after : Dynamic.Heap := ⟨[⟨mappingType, some (.mapping .bool .bool []), none⟩]⟩
private theorem initial : GenericHeap.HeapRepresents model [1] world before store ∧
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) [1] world [] scope sourceEnvironment environment ambient.definitions := by
  have empty := (GenericHeap.HeapRepresents.empty (model := model)).allocate_administrative administrativeTyped
  obtain ⟨heap, reference⟩ := empty.allocate (.uninitialized projected) Dynamic.Heap.Allocates.append
  exact ⟨heap, .cons reference (.nil .nil)⟩
private theorem locals : Dynamic.EnvironmentAgrees before context.locals sourceEnvironment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem actualTyped : RuntimeEnvironmentHasTypes world (.integer 99 :: administrativeValue :: environment)
    [.integer, administrativeType, .cell (OptionalCell.cellType nativeType)] ambient.definitions :=
  .cons .integer (.cons (administrativeTyped.weaken ⟨world, rfl⟩) (.cons (.cellRef rfl) .nil))
private def ξ : Renaming := Renaming.comp (Renaming.insertion 0) (Renaming.insertion 0)
private theorem agrees : EnvironmentsAgree ξ environment (.integer 99 :: administrativeValue :: environment) :=
  GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix (show EnvironmentsAgree Renaming.id environment environment from fun {_ _} found => found) administrativeValue) (.integer 99)
private theorem initialRead : Dynamic.ExpressionEvaluatesOutcome program context [] source sourceEnvironment before (id 2) (.value (.bool false)) after := by
  apply Dynamic.ExpressionEvaluatesOutcome.value
  apply Dynamic.ExpressionEvaluates.intro (raw := .bool false) (middle := after) (lookupExpression?_sound (node := indexNode) (by cbv))
  · change Dynamic.ExpressionFormEvaluates program context [] source sourceEnvironment before (.index (id 0) (id 1)) [] [] (.bool false) after
    apply Dynamic.ExpressionFormEvaluates.indexDefault (coercions := []) rfl
    · exact .intro (lookupExpression?_sound (node := baseNode) (by rfl))
        (.localEmptyMapping rfl .head (.intro .head) rfl rfl rfl (.intro (.intro .head) .head)) .nil
    · exact .intro (lookupExpression?_sound (node := keyNode) (by cbv)) (.builtinBoolean rfl) .nil
    · exact .nil
    · exact .bool
  · exact .nil

private theorem sourceTrace : Dynamic.FunctionStatementsExecuteOutcome program context [] source sourceEnvironment before
    statements context (.returned (.bool false)) after := by
  have first : Dynamic.ExpressionEvaluates program context [] source sourceEnvironment before (id 2) (.bool false) after := by
    cases initialRead with | value evaluated => exact evaluated
  have second : Dynamic.ExpressionEvaluates program context [] source sourceEnvironment after (id 2) (.bool false) after := by
    apply Dynamic.ExpressionEvaluates.intro (raw := .bool false) (middle := after) (lookupExpression?_sound (node := indexNode) rfl)
    · apply Dynamic.ExpressionFormEvaluates.indexDefault (coercions := []) rfl
      · exact .intro (lookupExpression?_sound (node := baseNode) rfl) (.local rfl .head (.intro .head) rfl rfl) .nil
      · exact .intro (lookupExpression?_sound (node := keyNode) rfl) (.builtinBoolean rfl) .nil
      · exact .nil
      · exact .bool
    · exact .nil
  exact .control (.cons (.expression (lookupStatement?_sound (node := discarded) rfl) rfl first)
    (.terminal (.returnValue (lookupStatement?_sound (node := returned) rfl) rfl second) (.returned _)))

/-- The first discarded index initializes the source mapping. The second
comparator captures its typed discarded value and the original ambient slots. -/
theorem accepted_preserves {code : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy 12 source scope statements .bool (fun _ => reason) reason reason = .ok code) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (.integer 99 :: administrativeValue :: environment) store (code.rename ξ) value finalStore ∧
      BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld faults .bool .bool (.returned (.bool false)) value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [1] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨flow, rfl, tree⟩ := certified accepted
  exact (Tree.body_preserves (values := values) functions (.refl _) program [] contextValid unique uninitialized missing
    tree reason reason initial.2 initial.1 locals agrees actualTyped sourceTrace).2

/-- Completion alone reconstructs the source statement trace, including
administrative helper allocations and the live mapping read after discard. -/
theorem accepted_reflects {code : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy 12 source scope statements .bool (fun _ => reason) reason reason = .ok code)
    {value : Value} {finalStore : Store}
    (completed : Evaluates (.integer 99 :: administrativeValue :: environment) store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context [] source sourceEnvironment before statements context outcome after ∧
      BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld faults .bool .bool outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [1] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨flow, rfl, tree⟩ := certified accepted
  exact Tree.body_reflects (values := values) functions (.refl _) program [] contextValid uninitialized missing
    tree reason reason initial.2 initial.1 locals agrees actualTyped completed

private def rawWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Item { Item(Word) }",
    "function repeated(m: mapping(Bool => Bool)) returns (Bool) { m[true]; return m[false]; }",
    "function lazy() returns (Bool) { let m: mapping(Bool => Bool); m[true]; return !m[false]; }",
    "function firstFailure() returns (Bool) { let m: mapping(Bool => Item); let n: mapping(Bool => Bool); m[true]; return n[false]; }",
    "function early() returns (Bool) { let m: mapping(Bool => Item); return true; m[true]; }",
    "function nested(m: mapping(Bool => mapping(Bool => Bool))) returns (Bool) { (m[true][false], !m[false][true]); return m[false][false] ? m[true][true] : !m[true][false]; }"]}] }

def run : IO Unit := do
  let generated ← SourceCompilerFeatureSupport.get "synthetic typed lowering" compiledResult
  let observed := Core.LanguageResult.observeResult (Core.runStateful 30000
    ⟨.eval (generated.rename ξ) (.integer 99 :: administrativeValue :: environment), [], store⟩)
  match observed with
  | .succeeded (.bool false) finalStore =>
      SourceCompilerFeatureSupport.require (finalStore[0]? == some administrativeValue)
        "typed discard changed the ambient closure cell"
  | _ => throw (IO.userError "actual synthetic typed lowering did not complete as false")
  let checked ← SourceCompilerFeatureSupport.get "typed statement checker" (checkProgram rawWorkspace)
  let repeated ← SourceCompilerFeatureSupport.compileNamed checked "repeated"
  let input : SourceCoreExecution.Value := .mapping .bool .bool [(.bool true, .bool false), (.bool false, .bool true)]
  SourceCompilerFeatureSupport.require ((← repeated.run [input]) == .bool true) "repeated index changed result"
  repeated.checkResume [input] (.bool true)
  let lazy ← SourceCompilerFeatureSupport.compileNamed checked "lazy"
  SourceCompilerFeatureSupport.require ((← lazy.run []) == .bool true) "lazy discarded index changed result"
  lazy.checkCells [] [(.mapping .bool .bool, some (.mapping .bool .bool []))]
  let failed ← SourceCompilerFeatureSupport.compileNamed checked "firstFailure"
  let invocation ← failed.invoke []
  match invocation.outcome with
  | .failed token _ =>
      match ← invocation.diagnostic token with
      | some {error := .typeMismatch _ none, span := some _, ..} => pure ()
      | _ => throw (IO.userError "discarded index lost its missing-default metadata/span")
  | _ => throw (IO.userError "discarded missing-default index did not fail")
  let failedState := SourceCompilerFeatureSupport.sourceState (← failed.audit [])
  match failedState.heap with
  | [first, second] =>
      SourceCompilerFeatureSupport.require (second.type == .mapping .bool .bool && second.value.isNone)
        "missing-default failure evaluated the remaining mapping read"
      match first.value with
      | some (.mapping .bool _ []) => pure ()
      | _ => throw (IO.userError "discarded index lost lazy root initialization")
  | _ => throw (IO.userError "discarded index changed source allocation order")
  let early ← SourceCompilerFeatureSupport.compileNamed checked "early"
  SourceCompilerFeatureSupport.require ((← early.run []) == .bool true) "return evaluated the unreachable missing-default index"
  let nested ← SourceCompilerFeatureSupport.compileNamed checked "nested"
  SourceCompilerFeatureSupport.require
    ((← nested.run [.mapping .bool (.mapping .bool .bool) []]) == .bool true) "nested typed expression statement changed result"
  IO.println "typed statements: discarded index captures, ambient closure, actual receipts, lazy default, early return and resume GREEN"
end Tests.SourceCoreTypedStatements
end

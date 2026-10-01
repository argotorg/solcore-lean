import Solcore.SourceSemantics.CoreLowering.BuiltinCallTypedCertificates
import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.Frontend.ProgramChecking

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

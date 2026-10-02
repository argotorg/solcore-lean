import Solcore.SourceSemantics.CoreLowering.BuiltinCallNativeTyping

/-! An actual builtin compiler result is typed without a lowering tree or a
native argument-typing premise. Its literal child is extracted from its real
callback. The existing builtin IO suites cover effects, ordering and resume. -/
set_option autoImplicit false
namespace Tests.SourceCoreBuiltinNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionScalarNativeTyping BuiltinCallNativeTyping

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"native_builtin", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "native_builtin.solc"⟩, 0, 1⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
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
private def reasonAt : ExpressionId → Word := fun _ => Word.zero
private def policy (native : SourceCoreGeneralFunctions.CallableContext) : SourceCoreFunctions.Policy :=
  {SourceCoreCompatibleDataExpressions.functionPolicy 100 values with
    callables := SourceCoreGeneralFunctions.callablePolicy (some native) []}

/-- The accepted compiler action fixes the exact callee, argument callback,
packed parameter check and gate. Hidden contexts and definitions are arbitrary. -/
theorem accepted_literal_builtin_native
    (native : SourceCoreGeneralFunctions.CallableContext)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.builtin .wordToInteger))
    {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody 3 compilation source [] (id 2) reasonAt = .ok code)
    (definitions : DataEnvironment) (administrative : Core.Context) :
    NativeTyping definitions administrative code := by
  apply of_functions native [] rfl descriptor (by rfl) (by rfl) (by cbv) (by rfl) (by rfl) _ accepted
  intro child member lowered generated
  have same : child = id 0 := by simpa using member
  subst child
  have literal := CompatibleExpressionLiterals.of_functions (values := values) (node := literalNode) (by rfl)
    (.word _) (by intro absent; cases absent) (by intros; rfl) rfl rfl generated
  obtain ⟨node, found, scalar⟩ := literal
  exact ⟨node, found, literal_native scalar definitions administrative⟩

/-- Every contracted builtin body is typed in an arbitrary surrounding
context; only the exact parameter bundle is used by the generated closure. -/
theorem every_builtin_contract_native (function : BuiltinFunctionId) (identity contract : Word)
    (definitions : DataEnvironment) (context : Core.Context) :
    HasType context (BuiltinCalls.Protocol.contracted function identity contract)
      (LanguageResult.resultType (CallableContract.functionType
        (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function))) definitions :=
  contracted_native function identity contract definitions context

end Tests.SourceCoreBuiltinNativeTyping

import Solcore.Test.SourceCoreChosenOrdinaryAcceptedNativeTyping
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedIssuedShell

/-! The accepted initializer selects its lambda Site once. Original native
typing, Source rows and diagnostic issuers construct its body collector inputs;
the fixed representation read budget remains separate from compiler fuel. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedLiteralFactory
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedLiteralReturnSiteShells
open CallableIndexedOwnedLiteralPlaceDiagnosticShells
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedPreparedMixedBodySiteInputs

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
    (atHeader : HeaderAt fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (metadata : SourceCoreChosenOrdinaryAcceptedBodyMetadata.Receipt fixture.packet fixture.graph)
    (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
    {compilation : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    {fuel : Nat} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (root : LiteralRootReceipt (compiled := fixture.packet.compiled) caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
      fuel (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1) reasonAt lowered)

/-- The approved domain is fixed before the compiler selects its Site. -/
def literalSyntax : TypedSource → ExpressionId → Prop :=
  fun _ id => id = expressionId fixture.packet 3

include atHeader in
/-- Genuine singleton return rows identify the collector's literal occurrence. -/
theorem inputs_expression
    (produced : Produced (compiled := fixture.packet.compiled) caller.named fixture.graph.parameters wordType
      [statementId fixture.packet 2] (runtimeContext fixture.packet) [] (initialScope fixture.packet)
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) caller)
      (expressionId fixture.packet 1) lowered)
    (inputs : PlaceDiagnosticBodyInputs produced root) :
    inputs.expression = expressionId fixture.packet 3 := by
  have statement : inputs.statement = statementId fixture.packet 2 := (List.cons.inj inputs.singleton).1.symm
  have found := inputs.statementFound
  rw [statement, atHeader.named] at found
  have node : inputs.statementNode = fixture.graph.returned :=
    Option.some.inj (found.symm.trans fixture.graph.returnedFound)
  have form := inputs.statementForm
  rw [node, fixture.graph.returnedForm] at form
  injection form with expression
  exact (Option.some.inj expression).symm

include atHeader in
theorem inputs_syntax
    (produced : Produced (compiled := fixture.packet.compiled) caller.named fixture.graph.parameters wordType
      [statementId fixture.packet 2] (runtimeContext fixture.packet) [] (initialScope fixture.packet)
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) caller)
      (expressionId fixture.packet 1) lowered)
    (inputs : PlaceDiagnosticBodyInputs produced root) :
    approved produced root inputs = literalSyntax fixture := by
  funext source id
  exact congrArg (fun expression => id = expression) (inputs_expression fixture atHeader root produced inputs)

include atHeader shape metadata inventory in
/-- One actual accepted action chooses its Site and builds the raw factory.
No Produced, native typing, body input package or execution law is supplied. -/
theorem chosen_at_root :
    ∃ receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller
        (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
        (runtimeContext fixture.packet) [] (initialScope fixture.packet) (expressionId fixture.packet 1) lowered,
      receipt.formation.produced.site.code.policy = root.root.selected.policy ∧
      receipt.formation.produced.site.code.lowerBody = root.root.selected.lowerBody ∧
      receipt.formation.produced.site.code.fuel = fuel ∧
      receipt.formation.produced.site.code.view = source caller.named ∧
      receipt.formation.produced.site.code.reasonAt = reasonAt ∧
      ChosenFactory root.root (literalSyntax fixture) receipt ∧
      receipt.formation.body.readFuel = fixture.packet.compiled.indexed.fuel := by
  have found : (source caller.named).lookupExpression? (expressionId fixture.packet 1) = some fixture.graph.lambdaNode := by
    simpa only [atHeader.named] using fixture.graph.lambdaFound
  have ordinary : fixture.packet.compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context fixture.packet.compiled.indexed caller.named).owner ∧
        binding.initializer = expressionId fixture.packet 1)) = none := by
    simpa only [atHeader.named, context, CompatibleNamedBody.bodyContext] using fixture.calls.lambdaOrdinary
  have sourceEq : source caller.named = source fixture.packet.named := congrArg source atHeader.named
  have pointwise := CallableIndexedOwnedContextualCompilerPolicyProfiles.lambda_policy root.root
    (scope := initialScope fixture.packet) (reasonAt := reasonAt) found fixture.graph.lambdaForm
    fixture.graph.lambdaRequirements fixture.graph.lambdaCoercions ordinary
  have accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
      (fuel + 1) (context fixture.packet.compiled.indexed caller.named) (source caller.named)
      (initialScope fixture.packet) (expressionId fixture.packet 1) reasonAt = .ok lowered :=
    sourceEq.symm ▸ root.root.selected.accepted
  obtain ⟨reported, read⟩ := CallableIndexedOwnedPreparedMixedBodySiteInputs.lambda_read root.root
    found fixture.graph.lambdaForm pointwise accepted
  have readMetadata := CompatibleExpressionReads.metadata_of_read read
  have rawType : fixture.graph.lambdaNode.type = FunctionValues.sourceType
      (closure caller.named fixture.graph.parameters wordType [statementId fixture.packet 2]
        (runtimeContext fixture.packet) [] []) := by
    rw [fixture.graph.lambdaType]
    simp only [FunctionValues.sourceType, closure, shape.parameters, List.map_cons, List.map_nil,
      shape.scheme, TypeSystem.Scheme.mono, TypeSystem.Ty.productMany]
  have rawOrdinary : Dynamic.OrdinaryRequirementLayout fixture.graph.lambdaNode.requirements
      fixture.graph.lambdaNode.coercions [] := by
    rw [Dynamic.OrdinaryRequirementLayout, fixture.graph.lambdaRequirements, fixture.graph.lambdaCoercions]
    rfl
  obtain ⟨certificate, receipt, policyEq, bodyEq, fuelEq, viewEq, reasonEq, _certificateEq,
      inputs, property, syntaxEq, certificatesEq, readFuelEq, entryEq⟩ :=
    CallableIndexedOwnedSamePolicyCompilerLeafReceipts.lambda_of_accepted_with_inputs root.root
      (runtimeContext fixture.packet) [] inventory.contracts (LambdaMetadataViews.MetadataView.refl _)
      found fixture.graph.lambdaForm rawType rawOrdinary fixture.graph.lambdaCoercions found rfl
      readMetadata.owner fixture.graph.lambdaRequirements fixture.graph.lambdaCoercions ordinary read accepted
      (SourceCoreChosenOrdinaryAcceptedNativeTyping.native_at_root fixture atHeader shape metadata root)
      (fun produced inputs => InputProperty root.root (literalSyntax fixture) produced inputs ∧
        inputs.readFuel = fixture.packet.compiled.indexed.fuel)
      (fun produced diagnosticsEq _codeEq _compilationEq policyEq bodyEq _fuelEq viewEq reasonEq => by
        obtain ⟨bodyInputs, ⟨shell⟩⟩ := SourceCoreChosenOrdinaryAcceptedIssuedShell.shell
          fixture atHeader shape metadata inventory root produced diagnosticsEq policyEq viewEq fixture.packet.compiled.indexed.fuel
        have syntaxEq := inputs_syntax fixture atHeader root produced bodyInputs
        have shell : SiteShell (literalSyntax fixture) produced := syntaxEq ▸ shell
        let fixed : SiteShell (literalSyntax fixture) produced := {shell with readFuel := fixture.packet.compiled.indexed.fuel}
        exact ⟨SiteShell.to_inputs root.root (literalSyntax fixture) produced fixed policyEq bodyEq reasonEq,
          SiteShell.input_property root.root (literalSyntax fixture) produced fixed policyEq bodyEq reasonEq, rfl⟩)
  exact ⟨receipt, policyEq, bodyEq, fuelEq, viewEq, reasonEq,
    ⟨inputs, property.1, syntaxEq, certificatesEq, readFuelEq, entryEq⟩, readFuelEq.trans property.2⟩

include atHeader shape metadata inventory in
/-- The original named compiler and initializer selector supply the whole
choice internally. The retained parent action is not selected as this root. -/
theorem chosen_initializer :
    ∃ actualCompilation : Compilation fixture.packet.compiled.indexed caller.named
        (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode,
      ∃ actualRoot : LiteralRootReceipt (compiled := fixture.packet.compiled) caller.named
          (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode actualCompilation
          498 (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1)
          ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
          fixture.calls.initializer,
        ∃ receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller
            (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode actualCompilation
            (runtimeContext fixture.packet) [] (initialScope fixture.packet) (expressionId fixture.packet 1) fixture.calls.initializer,
          receipt.formation.produced.site.code.policy = actualRoot.root.selected.policy ∧
          receipt.formation.produced.site.code.lowerBody = actualRoot.root.selected.lowerBody ∧
          receipt.formation.produced.site.code.fuel = 498 ∧
          receipt.formation.produced.site.code.view = source caller.named ∧
          receipt.formation.produced.site.code.reasonAt =
            (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key ∧
          ChosenFactory actualRoot.root (literalSyntax fixture) receipt ∧
          receipt.formation.body.readFuel = fixture.packet.compiled.indexed.fuel := by
  obtain ⟨originalCompilation⟩ := fixture.packet.named_compilation
  let originalRoot := fixture.calls.initializer_root originalCompilation
  let actualCompilation : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode :=
    atHeader.named.symm ▸ originalCompilation
  let actualRoot := Eq.rec
    (motive := fun (named : Named) (same : fixture.packet.named = named) =>
      LiteralRootReceipt (compiled := fixture.packet.compiled) named
        (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode
        (same ▸ originalCompilation) 498 (source fixture.packet.named) (initialScope fixture.packet)
        (expressionId fixture.packet 1)
        ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
        fixture.calls.initializer)
    originalRoot atHeader.named.symm
  exact ⟨actualCompilation, actualRoot, chosen_at_root fixture atHeader shape metadata inventory actualRoot⟩

end Tests.SourceCoreChosenOrdinaryAcceptedLiteralFactory

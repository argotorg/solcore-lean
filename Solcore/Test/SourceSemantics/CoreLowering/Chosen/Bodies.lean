import Solcore.Test.SourceSemantics.CoreLowering.Chosen.Admission
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ChosenLambdaBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LiteralReturns
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ChosenOrdinaryCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.FunctionCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredIndirectApplication
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredIndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.ExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRuntime
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionGeneralBuiltins
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedLexicalControl
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ChosenStoredCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NestedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRecursive
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeIndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionReads

/-!
# Chosen ordinary body tests

Arguments and bodies of the accepted ordinary call: literals, ordered pairs and outer bounds.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
/-! Retain bootstrap layout and empty Source lexical capture from the same
authentic Header constructor, together with its existing runtime evidence.
Native installer captures keep their actual globals and frame references. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering Core
open CallableIndexedNamedGeneration
open Tests.SourceCoreChosenOrdinaryAcceptedFixture
open Tests.SourceCoreChosenOrdinaryAcceptedHeader
open Tests.SourceCoreChosenOrdinaryAcceptedHeaderRuntimeEvidence

/-- Bootstrap fields retained by the same authentic Header constructor. -/
structure BootstrapEvidence (fixture : AcceptedFixture) (header : ActualHeader fixture) : Prop
    extends RuntimeEvidence fixture header where
  layouts : header.layouts = fixture.packet.compiled.indexed.layouts
  captured : header.function.captured = []

/-- The genuine selected Compilation is eliminated only into this Prop receipt.
All fields belong to the one original Header constructor. -/
theorem header_exists_with_bootstrap (fixture : AcceptedFixture) (selected : OriginalSelection fixture.packet)
    (checked : Metadata fixture.packet) : ∃ header : ActualHeader fixture, BootstrapEvidence fixture header := by
  obtain ⟨compilation⟩ := fixture.packet.named_compilation
  let function := RecursiveNamedPreparedSourceFrames.view fixture.packet.compiled.sourceProgram fixture.packet.named compilation.statements
  have frame := source_frame fixture selected checked compilation
  obtain ⟨row, _, prepared⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation
    fixture.packet.compiled fixture.packet.namedSelected
  have agreement := RecursiveNamedPreparedSourceFrames.agreement prepared compilation
  have namedInputs := checked.named_inputs
  have parameters : function.parameters = [] := checked.inputs
  have sameContext : function.context = runtimeContext fixture.packet := checked.view_context compilation.statements
  have extended : MonoBindersExtend function.source.owner function.context function.parameters [] (runtimeContext fixture.packet) := by
    rw [parameters, sameContext]
    exact .nil _
  have valid : CompatibleRuntimeContextValidity.Valid fixture.packet.named.specialized.function.solvedRequirements
      (runtimeContext fixture.packet) function.evidence := by
    refine ⟨rfl, ?_, ?_⟩
    · exact fixture.runtime.source_runtime.requirements
    · have covers := RecursiveNamedPreparedSourceFrames.empty_covers (program := fixture.packet.compiled.sourceProgram) checked.assumptions
      rw [← sameContext]
      exact covers
  have unique : NodeOccurrencesUnique function.source := fixture.runtime.source_runtime.graph.nodeOccurrencesUnique
  have parameterType : fixture.packet.named.signature.parameterType =
      SourceCoreCompatibleCatalog.packTypes (fixture.packet.named.inputs.map Prod.snd) := by
    rw [namedInputs, List.map_nil]
    exact checked.parameter
  let header := RecursiveNamedCatalog.Header.of_dictionary_body
    (values := .initial fixture.packet.compiled.compatible.checked)
    (function := function) (instantiation := CallableNamedMetadata.instantiation fixture.packet.named.specialized)
    (sourceBody := RecursiveNamedSpecializationBodyFacts.bodyInstance fixture.packet.compiled.sourceProgram fixture.packet.named.specialized)
    (frame := frame) (named := fixture.packet.named) (agreement := agreement)
    (ordinaryReturn := checked.ordinary) (ordinaryParameters := by intro binder member; rw [parameters] at member; cases member)
    (target := checked.target) (context := runtimeContext fixture.packet) (types := []) (bindings := fixture.packet.named.inputs)
    (parameters := agreement.parameters) (inputs := agreement.parameters) (extended := extended)
    (solved := fixture.packet.named.specialized.function.solvedRequirements)
    (reasonAt := (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
    (readFuel := fixture.packet.compiled.indexed.fuel) (output := fixture.packet.named.signature.resultType)
    (policy := policy fixture)
    (fuel := fixture.packet.compiled.indexed.fuel) (fellThrough := compilation.own.fellThroughReason)
    (escaped := compilation.own.table.escapedReason) (body := compilation.body) (parameterCode := compilation.parameterCode)
    (code := compilation.output) (layouts := fixture.packet.compiled.indexed.layouts)
    (owner := fixture.packet.named.signature.key) (active := []) (globals := fixture.packet.compiled.indexed.base.globals.length)
    (onError := fun error => .sourceAllocation (reprStr error)) (acceptedPrefix := compilation.parametersCompiled)
    (hook := compilation.hook) (definitions_eq := rfl) (registered := CallableIndexedAmbient.frame_registered fixture.packet.compiled.indexed)
    (valid := valid) (unique := unique) (parameterType := parameterType) (resultType := rfl)
    (representation := representation fixture.packet.compiled.indexed) (compiledFuel := fixture.packet.compiled.indexed.fuel)
    (compiled := fixture.packet.compiled.indexed.secondPass) (slot := 0) (selected := fixture.packet.namedSelected)
    (cached := fixture.packet.cached.trans (congrArg some compilation.emitted))
  obtain ⟨parentsEq, ownEq, statementsEq, bodyEq⟩ := fixture.calls.compilation_alignment compilation
  obtain ⟨parametersEq, outputEq⟩ := fixture.tail.compilation_alignment compilation
  refine ⟨header, ⟨⟨?_, rfl, rfl⟩, rfl, rfl⟩⟩
  refine ⟨rfl, rfl, rfl, sameContext, parameters, rfl, bodyEq, parametersEq, outputEq, rfl, rfl,
    fixture.calls.fuel, fixture.calls.fuel, statementsEq, rfl, ?_⟩
  simpa only [header, function, RecursiveNamedPreparedSourceFrames.view, ownEq, statementsEq, bodyEq,
    CallableIndexedNamedGeneration.source, bodyAction, SourceCoreGeneralFunctions.bodyLowererWithRepresentation,
    policy] using fixture.calls.bodyCompiled

/-- The checked fixture supplies the same authentic Header and runtime facts. -/
theorem header_fixture_with_bootstrap (given : HeaderFixture) :
    ∃ header : ActualHeader given.fixture,
      BootstrapEvidence given.fixture header :=
  header_exists_with_bootstrap given.fixture given.selected given.checked

end Tests.SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedLiteralFactory
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
theorem chosen_at_root
    (originalReasons : reasonAt = fixture.packet.diagnostics.program.reasonAt fixture.packet.named.signature.key) :
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
      ⟨fixture.packet.diagnostics, fixture.packet.diagnosticsFound,
        by unfold effectiveDiagnostics; split <;> exact ⟨rfl, rfl⟩⟩
      (runtimeContext fixture.packet) [] inventory.contracts (LambdaMetadataViews.MetadataView.refl _)
      found fixture.graph.lambdaForm rawType rawOrdinary fixture.graph.lambdaCoercions found rfl
      readMetadata.owner fixture.graph.lambdaRequirements fixture.graph.lambdaCoercions ordinary read accepted
      (SourceCoreChosenOrdinaryAcceptedNativeTyping.native_at_root fixture atHeader shape metadata root)
      (fun produced inputs => InputProperty root.root (literalSyntax fixture) produced inputs ∧
        inputs.readFuel = fixture.packet.compiled.indexed.fuel)
      (fun produced diagnosticsEq _codeEq _compilationEq policyEq bodyEq _fuelEq viewEq reasonEq => by
        have bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code caller.named := by
          apply CallableIndexedOwnedContextualLambdaProvenance.BodyReasons.of_issued fixture.packet.diagnosticsFound
          exact (reasonEq.trans originalReasons).trans
            (congrArg (fun named : Named => fixture.packet.diagnostics.program.reasonAt named.signature.key) atHeader.named.symm)
        obtain ⟨bodyInputs, ⟨shell⟩⟩ := SourceCoreChosenOrdinaryAcceptedIssuedShell.shell
          fixture atHeader shape metadata inventory root produced diagnosticsEq policyEq viewEq bodyReasons fixture.packet.compiled.indexed.fuel
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
  exact ⟨actualCompilation, actualRoot, chosen_at_root fixture atHeader shape metadata inventory actualRoot
    (by unfold effectiveDiagnostics; split <;> rfl)⟩

end Tests.SourceCoreChosenOrdinaryAcceptedLiteralFactory
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedLiteralSupport
/-! The selected initializer retains its original lambda indices and factory.
The actual literal inventory constructs local domains at current contexts;
existing compiler coverage consumes the same recaptured Support certificate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedLiteralSupport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedPreparedMixedBodySiteInputs
open CallableIndexedOwnedLiteralReturnSiteShells
open CallableIndexedOwnedLiteralPlaceDiagnosticShells

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
    (atHeader : HeaderAt fixture caller)
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (produced : Produced (compiled := fixture.packet.compiled) caller.named parameters result statements
      (runtimeContext fixture.packet) [] (initialScope fixture.packet)
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) caller)
      (expressionId fixture.packet 1) lowered)

include atHeader produced in
/-- The retained original lookup fixes the selected lambda's three indices. -/
theorem produced_shape : parameters = fixture.graph.parameters ∧ result = wordType ∧
    statements = [statementId fixture.packet 2] := by
  have found : (source caller.named).lookupExpression? (expressionId fixture.packet 1) =
      some fixture.graph.lambdaNode := by
    simpa only [atHeader.named] using fixture.graph.lambdaFound
  have sameNode := Produced.source_node caller produced found
  have form := produced.site.code.sourceForm
  rw [sameNode, fixture.graph.lambdaForm] at form
  change ExpressionForm.lambda fixture.graph.parameters wordType [statementId fixture.packet 2] =
    .lambda parameters result statements at form
  injection form with sameParameters sameResult sameStatements
  exact ⟨sameParameters.symm, sameResult.symm, sameStatements.symm⟩

variable (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (metadata : SourceCoreChosenOrdinaryAcceptedBodyMetadata.Receipt fixture.packet fixture.graph)
    (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
    {compilation : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    {rootFuel : Nat}
    (root : LiteralRootReceipt (compiled := fixture.packet.compiled) caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
      rootFuel (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1)
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
      lowered)

include atHeader shape metadata inventory in
/-- Only local index binders are substituted. The returned inputs retain the
original Produced value and its original diagnostic issuer. -/
theorem body_inputs_at_produced
    (diagnosticsEq : produced.diagnostics = effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
    (samePolicy : produced.site.code.policy = root.root.selected.policy)
    (sameView : produced.site.code.view = source caller.named)
    (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code caller.named) :
    Nonempty (PlaceDiagnosticBodyInputs produced root) := by
  obtain ⟨sameParameters, sameResult, sameStatements⟩ := produced_shape fixture atHeader produced
  subst parameters
  subst result
  subst statements
  exact SourceCoreChosenOrdinaryAcceptedIssuedShell.body_inputs fixture atHeader shape metadata inventory
    root produced diagnosticsEq samePolicy sameView bodyReasons

include atHeader in
/-- Every genuine singleton return input identifies the same approved literal. -/
theorem approved_is_literal (inputs : PlaceDiagnosticBodyInputs produced root) :
    approved produced root inputs = SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture := by
  obtain ⟨sameParameters, sameResult, sameStatements⟩ := produced_shape fixture atHeader produced
  subst parameters
  subst result
  subst statements
  exact SourceCoreChosenOrdinaryAcceptedLiteralFactory.inputs_syntax fixture atHeader root produced inputs

include atHeader in
/-- The approved occurrence excludes indirect calls while the outer parent
remains an actual indirect call in the same Source. -/
theorem no_indirect_on :
    CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn (source caller.named)
      (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture (source caller.named)) := by
  intro id node callee ids resolution allowed found
  change id = expressionId fixture.packet 3 at allowed
  have original : (source fixture.packet.named).lookupExpression? id = some node := by
    simpa only [atHeader.named] using found
  exact fixture.graph.body_no_indirect allowed original

variable
    (selected : OriginalSelection fixture.packet) (checked : Metadata fixture.packet)
    (receipt : Receipt caller (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
      fixture.packet.namedCode compilation (runtimeContext fixture.packet) [] (initialScope fixture.packet)
      (expressionId fixture.packet 1) lowered)
    (samePolicy : receipt.formation.produced.site.code.policy = root.root.selected.policy)
    (sameView : receipt.formation.produced.site.code.view = source caller.named)
    (readFuelEq : receipt.formation.body.readFuel = fixture.packet.compiled.indexed.fuel)

include atHeader shape metadata inventory selected checked samePolicy sameView readFuelEq in
/-- Runtime signatures at the actual current context supply the catalog field.
The selected Support's read budget is the original fixed indexed budget. -/
theorem domain_at_support (environment : Dynamic.Environment)
    (currentContext : SourceSemantics.Context) (currentScope : SourceCoreLocalCell.Scope)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked fixture.packet.compiled.sourceProgram)
      currentContext (receipt.formation.function environment).source) :
    DomainAt root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
      (receipt.formation.support environment).body.readFuel currentContext [] currentScope
      (SourceCoreChosenOrdinaryAcceptedCatalogFacts.headers caller) := by
  obtain ⟨inputs⟩ := body_inputs_at_produced fixture atHeader receipt.formation.produced shape metadata inventory
    root receipt.diagnostics_eq samePolicy sameView receipt.formation.bodyReasons
  have literal := approved_is_literal fixture atHeader receipt.formation.produced root inputs
  have domain := SourceCoreChosenOrdinaryAcceptedLiteralDomainGlobals.domain_at fixture atHeader selected checked
    inventory root receipt.formation.produced inputs currentContext currentScope runtime.signatures
  rw [literal] at domain
  change DomainAt root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
    receipt.formation.body.readFuel currentContext [] currentScope _
  rw [readFuelEq]
  exact domain

variable
    (chosen : ChosenFactory root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) receipt)

include chosen readFuelEq in
/-- Recapture retains the selected expression factory and its fixed read fuel. -/
theorem recaptured_factories (environment : Dynamic.Environment) :
    (receipt.formation.support environment).expressionSyntax =
      SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture ∧
    (receipt.formation.support environment).certificates =
      certificates root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) ∧
    (receipt.formation.support environment).body.readFuel = fixture.packet.compiled.indexed.fuel := by
  have actual := recaptured_factory root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
    receipt chosen environment
  exact ⟨actual.1, actual.2.1, actual.2.2.trans readFuelEq⟩

include atHeader shape metadata inventory selected checked samePolicy sameView readFuelEq chosen in
/-- The original compiler coverage consumes one actual accepted child from
the same recaptured Support; no completed expression or body law is supplied. -/
theorem tree_at_support (environment : Dynamic.Environment)
    (currentContext : SourceSemantics.Context) (currentScope : SourceCoreLocalCell.Scope)
    (valid : CompatibleRuntimeContextValidity.Valid
      (context fixture.packet.compiled.indexed caller.named).solvedRequirements currentContext [])
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked fixture.packet.compiled.sourceProgram)
      currentContext (receipt.formation.function environment).source)
    {child : ExpressionId} {output : SourceCoreBasic.LoweredExpr}
    (actual : (receipt.formation.support environment).certificates
      (receipt.formation.support environment).body.readFuel (receipt.formation.function environment).source
      currentContext currentScope child output) :
    let domain := domain_at_support fixture atHeader shape metadata inventory root selected checked receipt
      samePolicy sameView readFuelEq environment currentContext currentScope runtime
    RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor
      (ScopedBodyCalls root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
        (indirect_factory root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
          (SourceCoreChosenOrdinaryAcceptedCatalogFacts.headers caller) domain valid)
        (SourceCoreChosenOrdinaryAcceptedCatalogFacts.headers caller))
      receipt.formation.body.readFuel (.initial fixture.packet.compiled.compatible.checked)
      (source caller.named) currentContext (context fixture.packet.compiled.indexed caller.named).solvedRequirements
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
      currentScope child output := by
  let domain := domain_at_support fixture atHeader shape metadata inventory root selected checked receipt
    samePolicy sameView readFuelEq environment currentContext currentScope runtime
  exact support_cover_for root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
    receipt true chosen environment (SourceCoreChosenOrdinaryAcceptedCatalogFacts.headers caller) domain valid runtime actual

end Tests.SourceCoreChosenOrdinaryAcceptedLiteralSupport
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedInitializerAdmission
/-! The actual initializer lambda cannot fault: it copies the captured cells
and returns the closure over the copies. Its genuine raw closure typing and
initial admission retain every stable row. The chosen compiler receipt is
aligned through its original Source lookup. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedInitializerAdmission
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedOwnedOrdinaryLambdaSourceFacts CallableIndexedOwnedSourceAdmission

variable (fixture : AcceptedFixture)

/-- This is the exact Source lambda at occurrence one, with its actual captures. -/
def initializer (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment) : Dynamic.Closure :=
  closure fixture.packet.named fixture.graph.parameters wordType [statementId fixture.packet 2]
    (runtimeContext fixture.packet) evidence environment

variable (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment)

include shape in
/-- The genuine lambda judgment retains the actual raw function and body rows. -/
theorem source_facts : Facts (initializer fixture evidence environment)
    (expressionId fixture.packet 1) fixture.graph.lambdaNode := by
  exact of_typed fixture.runtime.source_runtime.graph.nodeOccurrencesUnique
    fixture.graph.lambdaFound fixture.graph.lambdaForm
    (SourceCoreChosenOrdinaryAcceptedTyping.lambda_typed shape) fixture.graph.lambdaCoercions

include shape in
/-- Covering evidence and the actual captured environment close the static
closure code; no whole-program execution theorem is used. -/
theorem value_has_type {heap : Dynamic.Heap}
    (covers : evidence.Covers (runtimeContext fixture.packet))
    (captures : Dynamic.EnvironmentAgrees heap (runtimeContext fixture.packet).locals environment) :
    Dynamic.ValueHasType (runtimeContext fixture.packet) heap
      (.closure (initializer fixture evidence environment)) fixture.graph.lambdaNode.type := by
  have facts := source_facts fixture shape evidence environment
  have frame := facts.frame fixture.runtime.source_runtime covers
  rw [facts.sourceType]
  exact .closure rfl frame.code covers captures

/-- The literal lambda constructor yields a real Source execution that copies
the captured cells and returns the closure over the copies, independently of
its native compiler budget. -/
theorem evaluates {before after : Dynamic.Heap} {captured : Dynamic.Environment}
    (snapshot : Dynamic.EnvironmentCopies (source fixture.packet.named) environment before captured after) :
    Dynamic.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (runtimeContext fixture.packet) evidence (source fixture.packet.named) environment before
      (expressionId fixture.packet 1) (.closure (initializer fixture evidence captured)) after := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound fixture.graph.lambdaFound)
  · rw [fixture.graph.lambdaForm]
    exact .lambda (by simp only [fixture.graph.lambdaRequirements, fixture.graph.lambdaCoercions]; rfl) snapshot
  · rw [fixture.graph.lambdaCoercions]
    exact .nil

private theorem value_of_facts {program : SourceSemantics.Program} {function : Dynamic.Closure}
    {id : ExpressionId} {node : ExpressionNode} (facts : Facts function id node)
    (unique : NodeOccurrencesUnique function.source) {before after : Dynamic.Heap} {value : Dynamic.Value}
    (trace : Dynamic.ExpressionEvaluates program function.context function.evidence
      function.source function.captured before id value after) :
    ∃ captured, value = .closure {function with captured := captured} ∧
      Dynamic.EnvironmentCopies function.source function.captured before captured after := by
  cases trace with
  | intro found raw coercions =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique facts.contains))
    subst same
    rw [facts.coercions] at coercions
    cases coercions
    rw [facts.form] at raw
    cases raw with
    | lambda _ snapshot => exact ⟨_, rfl, snapshot⟩
  | generalizedLocal found form _ _ _ _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique facts.contains))
    subst same
    rw [facts.form] at form
    cases form

private theorem fault_of_facts {program : SourceSemantics.Program} {function : Dynamic.Closure}
    {id : ExpressionId} {node : ExpressionNode} (facts : Facts function id node)
    (unique : NodeOccurrencesUnique function.source) {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (trace : Dynamic.ExpressionFaults program function.context function.evidence
      function.source function.captured before id reason after) : False := by
  cases trace with
  | missing absent => exact Dynamic.ExpressionAbsentIn.excludes_contains absent facts.contains
  | form found raw =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique facts.contains))
    subst same
    rw [facts.form] at raw
    cases raw
  | coercion found _ failed =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique facts.contains))
    subst same
    rw [facts.coercions] at failed
    cases failed
  | generalizedLocalRequirement found form _ _ _ _ _ _ _ | generalizedLocalCoercion found form _ _ _ _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique facts.contains))
    subst same
    rw [facts.form] at form
    cases form

include shape in
/-- Any actual initializer value trace copies the captured cells and returns
this same closure over the copies, at the copied heap. -/
theorem values_at {program : SourceSemantics.Program} {before after : Dynamic.Heap} {value : Dynamic.Value}
    (trace : Dynamic.ExpressionEvaluates program (runtimeContext fixture.packet) evidence
      (source fixture.packet.named) environment before (expressionId fixture.packet 1) value after) :
    ∃ captured, value = .closure (initializer fixture evidence captured) ∧
      Dynamic.EnvironmentCopies (source fixture.packet.named) environment before captured after :=
  value_of_facts (source_facts fixture shape evidence environment)
    fixture.runtime.source_runtime.graph.nodeOccurrencesUnique trace

include shape in
/-- Ordinary lambda formation with its actual empty coercions cannot fault. -/
theorem no_fault {program : SourceSemantics.Program} {size : Nat} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.ExpressionFaults program size (runtimeContext fixture.packet) evidence
      (source fixture.packet.named) environment before (expressionId fixture.packet 1) reason after) : False :=
  fault_of_facts (source_facts fixture shape evidence environment)
    fixture.runtime.source_runtime.graph.nodeOccurrencesUnique trace.sound

include shape in
/-- This retains the actual sized Source outcome without identifying its
size with the native lambda compiler or completion size. -/
theorem outcome_at {program : SourceSemantics.Program} {size : Nat} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size (runtimeContext fixture.packet) evidence
      (source fixture.packet.named) environment before (expressionId fixture.packet 1) outcome after) :
    ∃ captured, outcome = .value (.closure (initializer fixture evidence captured)) ∧
      Dynamic.EnvironmentCopies (source fixture.packet.named) environment before captured after := by
  cases trace with
  | value trace =>
    obtain ⟨captured, rfl, copies⟩ := values_at fixture shape evidence environment trace.sound
    exact ⟨captured, rfl, copies⟩
  | fault trace => exact False.elim (no_fault fixture shape evidence environment trace)

/-- The Source producer itself supplies a genuine finite execution size. -/
theorem has_size {before after : Dynamic.Heap} {captured : Dynamic.Environment}
    (snapshot : Dynamic.EnvironmentCopies (source fixture.packet.named) environment before captured after) :
    ∃ size, RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size (runtimeContext fixture.packet) evidence (source fixture.packet.named) environment before
      (expressionId fixture.packet 1) (.value (.closure (initializer fixture evidence captured))) after :=
  RecursiveNamedCallBounds.ExpressionOutcome.has_size (.value (evaluates fixture evidence environment snapshot))

section Admission
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
    {protocol : ProtectedStateTransition.Protocol.{u, 0} (CallableIndexedOwnedFunctionState.Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
    {index : ProtectedStateTransition.Index} (initial : protocol.State index)

include shape in
/-- The closure over an environment that agrees with this actual state is
admitted at it. Its deep heap typing and every row's own stable history come
from the initial admission. -/
theorem post_admission
    (covers : evidence.Covers (runtimeContext fixture.packet))
    (captures : Dynamic.EnvironmentAgrees index.heap (runtimeContext fixture.packet).locals environment)
    (admitted : Admission bridge (runtimeContext fixture.packet) initial) :
    PostAdmission bridge (runtimeContext fixture.packet) fixture.graph.lambdaNode.type
      (.value (.closure (initializer fixture evidence environment))) initial := by
  refine ⟨admitted.rows, ?_⟩
  intro value same
  cases same
  exact ⟨value_has_type fixture shape evidence environment covers captures, admitted.heap⟩

end Admission

section ActualReceipt
open CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts
variable {caller : ActualHeader fixture} (atHeader : HeaderAt fixture caller)
    {lowered : SourceCoreBasic.LoweredExpr}
    {compilation : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    (receipt : Receipt caller (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
      fixture.packet.namedCode compilation (runtimeContext fixture.packet) [] (initialScope fixture.packet)
      (expressionId fixture.packet 1) lowered)

include atHeader in
/-- Original lookup and Header identity align the actual selected receipt's
closure, including its captures. There is no representation inverse. -/
theorem receipt_function : receipt.formation.function environment = initializer fixture [] environment := by
  obtain ⟨parameters, result, statements⟩ :=
    SourceCoreChosenOrdinaryAcceptedLiteralSupport.produced_shape fixture atHeader receipt.formation.produced
  change closure caller.named _ _ _ (runtimeContext fixture.packet) [] environment = _
  rw [parameters, result, statements, atHeader.named]
  rfl

include atHeader shape in
/-- Raw Source typing is attached to the same actual selected function. -/
theorem receipt_value_has_type {heap : Dynamic.Heap}
    (captures : Dynamic.EnvironmentAgrees heap (runtimeContext fixture.packet).locals environment) :
    Dynamic.ValueHasType (runtimeContext fixture.packet) heap
      (.closure (receipt.formation.function environment)) fixture.graph.lambdaNode.type := by
  rw [receipt_function fixture environment atHeader receipt]
  exact value_has_type fixture shape [] environment
    (receipt.formation.support environment).body.frame.evidence_covers captures

include atHeader shape in
/-- The selected receipt has the same initializer outcome: the closure over the
copies, at the copied heap. -/
theorem receipt_outcome_at {size : Nat} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size (runtimeContext fixture.packet) [] (source caller.named) environment before
      (expressionId fixture.packet 1) outcome after) :
    ∃ captured, outcome = .value (.closure (receipt.formation.function captured)) ∧
      Dynamic.EnvironmentCopies (source caller.named) environment before captured after := by
  have original := trace
  rw [atHeader.named] at original
  obtain ⟨captured, sameValue, copies⟩ := outcome_at fixture shape [] environment original
  rw [← receipt_function fixture captured atHeader receipt] at sameValue
  rw [atHeader.named]
  exact ⟨captured, sameValue, copies⟩

include atHeader in
/-- The same selected receipt has a genuine initializer Source execution over
the copies of its captured cells. -/
theorem receipt_evaluates {before after : Dynamic.Heap} {captured : Dynamic.Environment}
    (snapshot : Dynamic.EnvironmentCopies (source caller.named) environment before captured after) :
    Dynamic.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (runtimeContext fixture.packet) [] (source caller.named) environment before
      (expressionId fixture.packet 1) (.closure (receipt.formation.function captured)) after := by
  rw [receipt_function fixture captured atHeader receipt, atHeader.named]
  rw [atHeader.named] at snapshot
  exact evaluates fixture [] environment snapshot

section ReceiptAdmission
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
    {protocol : ProtectedStateTransition.Protocol.{u, 0} (CallableIndexedOwnedFunctionState.Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
    {index : ProtectedStateTransition.Index} (initial : protocol.State index)

include atHeader shape in
/-- Covering evidence comes from the actual recaptured static frame. The raw
closure and success admission refer to this same receipt and initial state. -/
theorem receipt_post_admission
    (captures : Dynamic.EnvironmentAgrees index.heap (runtimeContext fixture.packet).locals environment)
    (admitted : Admission bridge (runtimeContext fixture.packet) initial) :
    PostAdmission bridge (runtimeContext fixture.packet) fixture.graph.lambdaNode.type
      (.value (.closure (receipt.formation.function environment))) initial := by
  refine ⟨admitted.rows, ?_⟩
  intro value same
  cases same
  exact ⟨receipt_value_has_type fixture shape environment atHeader receipt captures, admitted.heap⟩

end ReceiptAdmission

end ActualReceipt
end Tests.SourceCoreChosenOrdinaryAcceptedInitializerAdmission
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedLiteralCompilerReceipts
/-! The retained initializer supplies the actual singleton-return compiler
receipt. Its approved child has admitted Word meaning at the same chosen
support, using the fixture's genuine numeric row and current runtime ledger. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedLiteralCompilerReceipts
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedPreparedMixedBodySiteInputs
open CallableIndexedOwnedLiteralReturnSiteShells
open CallableIndexedOwnedLiteralPlaceDiagnosticShells
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
    (atHeader : HeaderAt fixture caller)

include atHeader in
/-- The same Source lookup and original initializer inventory supply every
Word-literal field; no expression or body meaning is assumed. -/
theorem word_facts :
    CallableIndexedOwnedChosenWordLiteralExpressionBounds.WordNodeFacts
      (caller := caller) (expressionId fixture.packet 3) fixture.graph.literal := by
  refine ⟨?_, Or.inr ⟨_, _, fixture.graph.literalForm⟩, fixture.graph.literalType,
    fixture.graph.literalCoercions, ⟨_, fixture.graph.literalOwned⟩,
    Or.inr ⟨_, _, fixture.graph.literalForm⟩, ?_⟩
  · simpa only [atHeader.named] using fixture.graph.literalFound
  · simpa only [atHeader.named, context, CompatibleNamedBody.bodyContext] using fixture.calls.literalOrdinary

variable {lowered : SourceCoreBasic.LoweredExpr}
    {compilation : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    {rootFuel : Nat}
    (root : LiteralRootReceipt (compiled := fixture.packet.compiled) caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
      rootFuel (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1)
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
      lowered)
    (receipt : Receipt caller (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
      fixture.packet.namedCode compilation (runtimeContext fixture.packet) [] (initialScope fixture.packet)
      (expressionId fixture.packet 1) lowered)

include atHeader in
/-- The actual selected return is identified with occurrence 3 before its
original accepted body is inverted once. The result retains compiler fuel. -/
theorem compiler_receipt
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (metadata : SourceCoreChosenOrdinaryAcceptedBodyMetadata.Receipt fixture.packet fixture.graph)
    (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
    (samePolicy : receipt.formation.produced.site.code.policy = root.root.selected.policy)
    (sameView : receipt.formation.produced.site.code.view = source caller.named) :
    Nonempty (CallableIndexedOwnedSingletonReturnCompilerReceipts.Receipt
      receipt.formation.produced (expressionId fixture.packet 3)) := by
  obtain ⟨inputs⟩ := SourceCoreChosenOrdinaryAcceptedLiteralSupport.body_inputs_at_produced
    fixture atHeader receipt.formation.produced shape metadata inventory root
    receipt.diagnostics_eq samePolicy sameView receipt.formation.bodyReasons
  have literal := SourceCoreChosenOrdinaryAcceptedLiteralSupport.approved_is_literal
    fixture atHeader receipt.formation.produced root inputs
  have sameExpression : inputs.expression = expressionId fixture.packet 3 := by
    have allowed : approved receipt.formation.produced root inputs (source caller.named) inputs.expression := rfl
    rw [literal] at allowed
    exact allowed
  have read : (bodyPolicy receipt.formation.produced.compilation receipt.formation.produced.site.code).readStatement
      receipt.formation.produced.site.code.view inputs.statement = .ok (inputs.statementNode, inputs.statementCore) := by
    rw [read_policy, inputs.canonical]
    simp [SourceCoreCompatibleDataExpressions.readStatement, inputs.statementOwner,
      inputs.statementFound, inputs.statementProjected]
    rfl
  have accepted := CallableIndexedOwnedSingletonReturnCompilerReceipts.of_return
    receipt.formation.produced inputs.singleton read inputs.statementForm
  rw [sameExpression] at accepted
  exact accepted

variable (chosen : ChosenFactory root.root
    (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) receipt)

include atHeader chosen in
/-- A real accepted child at the same recaptured support supplies the original
literal runtime certificate, with its fixed approved occurrence. -/
theorem certificate_at_support (environment : Dynamic.Environment)
    {currentContext : SourceSemantics.Context} {childScope : SourceCoreLocalCell.Scope}
    {child : ExpressionId} {output : SourceCoreBasic.LoweredExpr}
    (actual : (receipt.formation.support environment).certificates
      (receipt.formation.support environment).body.readFuel (receipt.formation.function environment).source
      currentContext childScope child output) :
    child = expressionId fixture.packet 3 ∧ CompatibleExpressionLiteralRuntime.Certificate
      (context fixture.packet.compiled.indexed caller.named).solvedRequirements
      (receipt.formation.function environment).source child output := by
  exact CallableIndexedOwnedChosenWordLiteralExpressionBounds.certificate_at_support
    root (expressionId fixture.packet 3) fixture.graph.literal receipt chosen environment
    (word_facts fixture atHeader) actual

section Admitted
universe u
variable {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (currentContext : SourceSemantics.Context) (currentEvidence : Dynamic.EvidenceEnvironment)
    (ledger : currentContext.solvedRequirements = (context fixture.packet.compiled.indexed caller.named).solvedRequirements)
    (runtime : RuntimeRequirementLedgerValid currentContext)

include atHeader chosen ledger runtime in
/-- The original literal producer consumes the actual Source child once and
retains the same current state, all rows and successful Word admission. -/
theorem preserves_at_support (environment : Dynamic.Environment)
    (unique : NodeOccurrencesUnique (receipt.formation.function environment).source) (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
      currentContext currentEvidence (receipt.formation.function environment).source
      ((receipt.formation.support environment).certificates
        (receipt.formation.support environment).body.readFuel
        (receipt.formation.function environment).source currentContext) faults size := by
  exact CallableIndexedOwnedChosenWordLiteralExpressionBounds.preserves_at_support
    root (expressionId fixture.packet 3) fixture.graph.literal receipt chosen environment
    (word_facts fixture atHeader) bridge functions currentContext currentEvidence ledger runtime unique size

include atHeader chosen ledger runtime in
/-- Native reflection preserves the same actual tuple and reconstructs its
independently sized Source trace through the original literal producer once. -/
theorem reflects_at_support (environment : Dynamic.Environment) (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
      currentContext currentEvidence (receipt.formation.function environment).source
      ((receipt.formation.support environment).certificates
        (receipt.formation.support environment).body.readFuel
        (receipt.formation.function environment).source currentContext) faults size := by
  exact CallableIndexedOwnedChosenWordLiteralExpressionBounds.reflects_at_support
    root (expressionId fixture.packet 3) fixture.graph.literal receipt chosen environment
    (word_facts fixture atHeader) bridge functions currentContext currentEvidence ledger runtime size

end Admitted
end Tests.SourceCoreChosenOrdinaryAcceptedLiteralCompilerReceipts
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedLiteralInvocation
/-! The accepted fixture validates the actual recaptured entry against its
original lambda occurrence and parameter extension. Runtime invocation ports
retain the same chosen compiler receipt rather than selecting another Site. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedLiteralInvocation
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
    (atHeader : HeaderAt fixture caller)
    {lowered : SourceCoreBasic.LoweredExpr}
    {compilation : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    (receipt : Receipt caller (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
      fixture.packet.namedCode compilation (runtimeContext fixture.packet) [] (initialScope fixture.packet)
      (expressionId fixture.packet 1) lowered)
    (environment : Dynamic.Environment)

include atHeader in
/-- The same actual Source lookup fixes the recaptured function indices. -/
theorem support_shape :
    (receipt.formation.function environment).parameters = fixture.graph.parameters ∧
    (receipt.formation.function environment).resultType = wordType ∧
    (receipt.formation.function environment).body = [statementId fixture.packet 2] := by
  exact SourceCoreChosenOrdinaryAcceptedLiteralSupport.produced_shape fixture atHeader receipt.formation.produced

include atHeader in
/-- The retained return node belongs to the same recaptured function Source. -/
theorem return_found :
    (receipt.formation.function environment).source.lookupStatement? (statementId fixture.packet 2) =
      some fixture.graph.returned := by
  change (source caller.named).lookupStatement? _ = _
  simpa only [atHeader.named] using fixture.graph.returnedFound

variable (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)

include atHeader shape in
/-- Original monomorphic parameter installation identifies the actual native
entry types, independently of any execution or packed-value inverse. -/
theorem body_types :
    (receipt.formation.support environment).body.types = [parameterType] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq
    (receipt.formation.support environment).body.extended
  rw [(support_shape fixture atHeader receipt environment).1, shape.parameters] at types
  simpa only [List.map_cons, List.map_nil, shape.scheme, TypeSystem.Scheme.mono] using types.symm

include atHeader shape in
/-- Functional binder extension aligns the actual entry context with the
fixture's genuine parameter context; capture changes only the environment. -/
theorem body_context :
    (receipt.formation.support environment).body.context = shape.bodyContext := by
  have actual := (receipt.formation.support environment).body.extended
  rw [(support_shape fixture atHeader receipt environment).1,
    body_types fixture atHeader receipt environment shape] at actual
  have original : MonoBindersExtend (source caller.named).owner (runtimeContext fixture.packet)
      fixture.graph.parameters [parameterType] shape.bodyContext := by
    simpa only [atHeader.named] using shape.parameters_extend
  exact Dynamic.MonoBindersExtend.functional actual original

include atHeader shape in
/-- The entry retains the actual solved numeric rows, so runtime requirement
validity is derived for this context rather than supplied as a body law. -/
theorem body_runtime :
    RuntimeRequirementLedgerValid (receipt.formation.support environment).body.context := by
  rw [body_context fixture atHeader receipt environment shape]
  exact numeric_runtime_ledger fixture.runtime.rows


variable {rootFuel : Nat}
    (root : CallableIndexedOwnedLiteralReturnSiteShells.LiteralRootReceipt (compiled := fixture.packet.compiled) caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
      rootFuel (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1)
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
      lowered)
    (chosen : CallableIndexedOwnedPreparedMixedBodySiteInputs.ChosenFactory root.root
      (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) receipt)

section Invocation
universe u
variable {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    {mapping : LocationMap} {world : StoreTyping} {actualEnvironment : Environment}
    (captured : Captures fixture.packet.compiled.indexed mapping world (initialScope fixture.packet)
      (receipt.formation.function []).captured actualEnvironment)
    (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
      (values := .initial fixture.packet.compiled.compatible.checked) caller)
    (history : CallableIndexedLambdaValues.History (receipt.formation.code []))
    (origin : SourceOrigin (receipt.formation.support []) history)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := fixture.packet.compiled.indexed)
      (values := .initial fixture.packet.compiled.compatible.checked)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      headers owner.key.locations 1 (initialScope fixture.packet) captured.canonical owner.key.frameLocation)
    {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
    {callerScope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (first : CallableIndexedOwnedFunctionState.State headers keys
      ⟨callerScope, mapping, world, before, store, canonical⟩)
    (beforeTyped : Dynamic.HeapWellTyped (runtimeContext fixture.packet) before)
    (argumentsTyped : Dynamic.ValuesHaveTypes (runtimeContext fixture.packet) before arguments [parameterType])
    (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows first)
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
      mapping world (receipt.formation.code []).receipt.loweredParameters arguments nativeArguments)
    (heaps : CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry functions
      mapping world before store)
    (reference : captured.canonical[(receipt.formation.code []).referenceIndex]? =
      some (.cellRef fixture.packet.compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))

include atHeader shape chosen origin observed beforeTyped argumentsTyped stable represented heaps reference in
/-- The fixture's actual Source and parameter rows instantiate the original
literal invocation port; capture, history and current pool remain genuine. -/
theorem invocation_preserves (budget : Nat)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) size
      callContext callerEvidence (receipt.formation.function []).evidence before
      (.closure (receipt.formation.function [])) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues nativeArguments :: encode fixture.packet.compiled.indexed.ancestry.layout.frame history.native :: actualEnvironment)
        store ((receipt.formation.code []).body.rename captured.embedding.lift.lift) value finalStore ∧
      CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt (registry := registry) (faults := faults)
        (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt [] captured prefixContext)
        (receipt.formation.code []) functions first outcome after value finalStore finalMap finalWorld  := by
  have actualArguments : Dynamic.ValuesHaveTypes (receipt.formation.function []).context
      before arguments (receipt.formation.support []).body.types := by
    rw [body_types fixture atHeader receipt [] shape]
    exact argumentsTyped
  have locals : Dynamic.EnvironmentAgrees before (receipt.formation.function []).context.locals
      (receipt.formation.function []).captured := .nil
  exact CallableIndexedOwnedLiteralLambdaInvocationBounds.invocation_preserves
    (literalRoot := root) (literalId := expressionId fixture.packet 3) (node := fixture.graph.literal)
    (receipt := receipt) (chosen := chosen) (capturedEnvironment := [])
    (facts := SourceCoreChosenOrdinaryAcceptedLiteralCompilerReceipts.word_facts fixture atHeader)
    (functions := functions) (found := return_found fixture atHeader receipt [])
    (form := fixture.graph.returnedForm) (singleton := (support_shape fixture atHeader receipt []).2.2)
    (owner := owner) (captured := captured) (prefixContext := prefixContext) (history := history)
    (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped)
    (argumentsTyped := actualArguments) (stable := stable) (represented := represented)
    (heaps := heaps) (locals := locals) (reference := reference) budget trace within

include atHeader shape chosen origin observed beforeTyped argumentsTyped stable represented heaps reference in
/-- The fixture's actual Source and parameter rows instantiate the original
literal invocation port; capture, history and current pool remain genuine. -/
theorem invocation_reflects (budget : Nat)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues nativeArguments :: encode fixture.packet.compiled.indexed.ancestry.layout.frame history.native :: actualEnvironment)
        store ((receipt.formation.code []).body.rename captured.embedding.lift.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) sourceSize
        callContext callerEvidence (receipt.formation.function []).evidence before
        (.closure (receipt.formation.function [])) arguments outcome after ∧
      CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt (registry := registry) (faults := faults)
        (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt [] captured prefixContext)
        (receipt.formation.code []) functions first outcome after value finalStore finalMap finalWorld  := by
  have actualArguments : Dynamic.ValuesHaveTypes (receipt.formation.function []).context
      before arguments (receipt.formation.support []).body.types := by
    rw [body_types fixture atHeader receipt [] shape]
    exact argumentsTyped
  have locals : Dynamic.EnvironmentAgrees before (receipt.formation.function []).context.locals
      (receipt.formation.function []).captured := .nil
  exact CallableIndexedOwnedLiteralLambdaInvocationBounds.invocation_reflects
    (literalRoot := root) (literalId := expressionId fixture.packet 3) (node := fixture.graph.literal)
    (receipt := receipt) (chosen := chosen) (capturedEnvironment := [])
    (facts := SourceCoreChosenOrdinaryAcceptedLiteralCompilerReceipts.word_facts fixture atHeader)
    (functions := functions) (found := return_found fixture atHeader receipt [])
    (form := fixture.graph.returnedForm) (singleton := (support_shape fixture atHeader receipt []).2.2)
    (owner := owner) (captured := captured) (prefixContext := prefixContext) (history := history)
    (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped)
    (argumentsTyped := actualArguments) (stable := stable) (represented := represented)
    (heaps := heaps) (locals := locals) (reference := reference) budget completed within

include atHeader shape chosen origin observed beforeTyped argumentsTyped stable represented heaps reference in
/-- The fixture's actual Source and parameter rows instantiate the original
literal invocation port; capture, history and current pool remain genuine. -/
theorem application_preserves (budget : Nat)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) size
      callContext callerEvidence (receipt.formation.function []).evidence before
      (.closure (receipt.formation.function [])) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [CallableIndexedLambdaValues.value (receipt.formation.code []) captured.embedding history.native actualEnvironment,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt (registry := registry) (faults := faults)
        (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt [] captured prefixContext)
        (receipt.formation.code []) functions first outcome after value finalStore finalMap finalWorld  := by
  have actualArguments : Dynamic.ValuesHaveTypes (receipt.formation.function []).context
      before arguments (receipt.formation.support []).body.types := by
    rw [body_types fixture atHeader receipt [] shape]
    exact argumentsTyped
  have locals : Dynamic.EnvironmentAgrees before (receipt.formation.function []).context.locals
      (receipt.formation.function []).captured := .nil
  exact CallableIndexedOwnedLiteralLambdaInvocationBounds.application_preserves
    (literalRoot := root) (literalId := expressionId fixture.packet 3) (node := fixture.graph.literal)
    (receipt := receipt) (chosen := chosen) (capturedEnvironment := [])
    (facts := SourceCoreChosenOrdinaryAcceptedLiteralCompilerReceipts.word_facts fixture atHeader)
    (functions := functions) (found := return_found fixture atHeader receipt [])
    (form := fixture.graph.returnedForm) (singleton := (support_shape fixture atHeader receipt []).2.2)
    (owner := owner) (captured := captured) (prefixContext := prefixContext) (history := history)
    (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped)
    (argumentsTyped := actualArguments) (stable := stable) (represented := represented)
    (heaps := heaps) (locals := locals) (reference := reference) budget trace within

include atHeader shape chosen origin observed beforeTyped argumentsTyped stable represented heaps reference in
/-- The fixture's actual Source and parameter rows instantiate the original
literal invocation port; capture, history and current pool remain genuine. -/
theorem application_reflects (budget : Nat)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [CallableIndexedLambdaValues.value (receipt.formation.code []) captured.embedding history.native actualEnvironment,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) sourceSize
        callContext callerEvidence (receipt.formation.function []).evidence before
        (.closure (receipt.formation.function [])) arguments outcome after ∧
      CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt (registry := registry) (faults := faults)
        (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt [] captured prefixContext)
        (receipt.formation.code []) functions first outcome after value finalStore finalMap finalWorld  := by
  have actualArguments : Dynamic.ValuesHaveTypes (receipt.formation.function []).context
      before arguments (receipt.formation.support []).body.types := by
    rw [body_types fixture atHeader receipt [] shape]
    exact argumentsTyped
  have locals : Dynamic.EnvironmentAgrees before (receipt.formation.function []).context.locals
      (receipt.formation.function []).captured := .nil
  exact CallableIndexedOwnedLiteralLambdaInvocationBounds.application_reflects
    (literalRoot := root) (literalId := expressionId fixture.packet 3) (node := fixture.graph.literal)
    (receipt := receipt) (chosen := chosen) (capturedEnvironment := [])
    (facts := SourceCoreChosenOrdinaryAcceptedLiteralCompilerReceipts.word_facts fixture atHeader)
    (functions := functions) (found := return_found fixture atHeader receipt [])
    (form := fixture.graph.returnedForm) (singleton := (support_shape fixture atHeader receipt []).2.2)
    (owner := owner) (captured := captured) (prefixContext := prefixContext) (history := history)
    (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped)
    (argumentsTyped := actualArguments) (stable := stable) (represented := represented)
    (heaps := heaps) (locals := locals) (reference := reference) budget completed within

end Invocation
end Tests.SourceCoreChosenOrdinaryAcceptedLiteralInvocation
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedLiteralCallGuard
/-! The original selected closure contract admits the actual singleton pair
argument and Word result. Caller stages and the authentic dispatch remain
unchanged; no verdict or execution premise is supplied. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedLiteralCallGuard
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts

variable (fixture : AcceptedFixture) (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)

/-- The retained parameter is an ordinary physical pair, independently of
its native projection or the caller's expression stages. -/
theorem parameter_runtime :
    ¬ Staging.CallGuard.RequiresComptime false shape.parameter := by
  rintro (force | staged | type)
  · cases force
  · rw [shape.ordinary] at staged
    cases staged
  · rw [shape.scheme] at type
    cases type

include shape in
/-- Source order and the original singleton parameter close the argument
stage judgment for every authentic caller frame. -/
theorem arguments_accept (frame : Staging.CallGuard.Frame) :
    Staging.CallGuard.ArgumentsAccept frame false 0 fixture.graph.parameters
      [expressionId fixture.packet 6] := by
  rw [shape.parameters]
  exact .cons (.ordinary (parameter_runtime fixture shape)) (.nil _)

include shape in
/-- The actual ordinary contract is accepted even when the caller itself
has an effectful stage. No stage lookup or replacement contract is used. -/
theorem contract_accepts (frame : Staging.CallGuard.Frame) (call : ExpressionId) :
    Staging.CallGuard.Accepts frame ⟨fixture.graph.parameters, false⟩ call
      [expressionId fixture.packet 6] := by
  classical
  by_cases effectful : Staging.CallGuard.Effectful frame
  · exact .effectful effectful
  · exact .ordinary effectful (arguments_accept fixture shape frame) (.ordinary rfl)

include shape in
/-- Binding the selected original contract to this Source closure supplies
its actual parameter list and ordinary Word result flag. -/
theorem stage_accepts {sidecar : SourceCoreStageContracts.Sidecar}
    {function : Dynamic.Closure} {contract : Staging.CallGuard.Contract}
    (parameters : function.parameters = fixture.graph.parameters)
    (result : function.resultType = wordType)
    (bound : (CallableLedger.frame sidecar).Binds (.closure function) contract)
    (call : ExpressionId) :
    Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) call
      [expressionId fixture.packet 6] (.closure function) := by
  have raw : CallableLedger.Binds sidecar.plan (.closure function) contract := bound
  cases raw with
  | closure actualParameters actualResult =>
      have ordinary : contract.stagedResult = false := by
        cases staged : contract.stagedResult with
        | false => rfl
        | true =>
            have impossible := actualResult.mp staged
            rw [result] at impossible
            cases impossible
      have same : contract = ⟨fixture.graph.parameters, false⟩ := by
        cases contract
        simp only at actualParameters ordinary
        cases actualParameters.trans parameters
        cases ordinary
        rfl
      exact .contract bound (same ▸ contract_accepts fixture shape _ call)

variable {caller : ActualHeader fixture} (atHeader : HeaderAt fixture caller)
    {lowered : SourceCoreBasic.LoweredExpr}
    {compilation : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    (receipt : Receipt caller (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
      fixture.packet.namedCode compilation (runtimeContext fixture.packet) [] (initialScope fixture.packet)
      (expressionId fixture.packet 1) lowered)
    {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
    {carrier : Value}
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) site site.call
      [expressionId fixture.packet 6] (.closure (receipt.formation.function [])) carrier)

include atHeader shape in
/-- The original lambda lookup identifies the actual physical count. -/
theorem physical_arity :
    (receipt.formation.function []).parameters.length = [expressionId fixture.packet 6].length := by
  rw [(SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader receipt []).1,
    shape.parameters]
  rfl

include atHeader shape in
/-- The exact sealed row accepts before arguments from the authentic bound
contract. Acceptance is proved rather than supplied as a gate verdict. -/
theorem before_arguments : dispatch.row.beforeArguments = .ok () := by
  have actual := SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader receipt []
  exact dispatch.accepted (stage_accepts fixture shape actual.1 actual.2.1 dispatch.bound site.call)

include atHeader shape in
/-- The same selected row accepts its physical arity and application gates.
The original codebook, sidecar and selected entry remain genuine inputs. -/
theorem accepted_at_selected {callee : ExpressionId} {metadata : IndirectCallResolution} {node : ExpressionNode}
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee
      [expressionId fixture.packet 6] metadata node dispatch.row) (unknown : Word) :
    CallableIndexedOwnedChosenOrdinarySelectedCallReceipts.AcceptedAt dispatch unknown := by
  have actual := SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader receipt []
  exact CallableIndexedOwnedChosenOrdinarySelectedCallReceipts.accepted_at_row dispatch selected unknown
    (stage_accepts fixture shape actual.1 actual.2.1 dispatch.bound site.call)
    (physical_arity fixture shape atHeader receipt)

end Tests.SourceCoreChosenOrdinaryAcceptedLiteralCallGuard
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedLiteralStoredApplication
/-! The accepted fixture's actual ordered pair supplies the raw call arguments.
At the genuine current argument state, its chosen singleton-return invocation
closes the original fourth bind without a whole-body or family meaning input.
The original physical restoration is performed by the invocation producer. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedLiteralStoredApplication
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters

variable (fixture : AcceptedFixture)

/-- The one actual argument occurrence fixes its value and unchanged Source
heap; this is an inversion of the retained Source trace, not a new execution. -/
theorem arguments_at {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {size : Nat}
    (trace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
      (source fixture.packet.named) environment before [expressionId fixture.packet 6] arguments after) :
    arguments = [SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argumentValue] ∧ after = before := by
  cases trace.sound with
  | cons head tail =>
    obtain ⟨sameValue, sameHeap⟩ := SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argument_outcome fixture (.value head)
    cases sameHeap
    cases Dynamic.ExpressionOutcome.value.inj sameValue
    cases tail
    exact ⟨rfl, rfl⟩

variable {caller : ActualHeader fixture} (atHeader : HeaderAt fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
    {lambdaLowered : SourceCoreBasic.LoweredExpr}
    {compilation : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    (receipt : Receipt caller (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
      fixture.packet.namedCode compilation (runtimeContext fixture.packet) [] (initialScope fixture.packet)
      (expressionId fixture.packet 1) lambdaLowered)
    {rootFuel : Nat}
    (root : CallableIndexedOwnedLiteralReturnSiteShells.LiteralRootReceipt (compiled := fixture.packet.compiled) caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
      rootFuel (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1)
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
      lambdaLowered)
    (chosen : CallableIndexedOwnedPreparedMixedBodySiteInputs.ChosenFactory root.root
      (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) receipt)

/-- The actual selected numeric row rules out every fault of the returned
literal and fixes its unchanged heap in the genuine parameter context. -/
private theorem literal_outcome {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      shape.bodyContext [] (source fixture.packet.named) environment before
      (expressionId fixture.packet 3) outcome after) :
    outcome = .value (.word (Word.ofNatModulo 7)) ∧ after = before := by
  have unique := fixture.runtime.source_runtime.graph.nodeOccurrencesUnique
  have found := fixture.graph.literalFound
  have sameNode : ∀ other, ContainsExpression (source fixture.packet.named) (expressionId fixture.packet 3) other →
      other = fixture.graph.literal := by
    intro other contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have nonlocal : ∀ name binder, fixture.graph.literal.form ≠ .reference name (.local binder) := by
    intros
    rw [fixture.graph.literalForm]
    simp
  have proves := numeric_requirement (context := shape.bodyContext) fixture.runtime.rows (Or.inl rfl)
  have selected : NumericLiteralEvidenceReceipts.Selected numericRows literalResolution (.builtin .intWord) :=
    ⟨wordRequirement 0, by simp [numericRows, wordRequirement, literalResolution], rfl, rfl⟩
  have safe := selected.safe (context := shape.bodyContext) fixture.runtime.rows
    (numeric_runtime_ledger (context := shape.bodyContext) fixture.runtime.rows) []
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro other raw path =>
      have same := sameNode _ other
      subst same
      rw [fixture.graph.literalCoercions] at path
      cases path
      rw [fixture.graph.literalForm] at raw
      cases raw with
      | integerLiteral _ constructed =>
        have expected : Dynamic.ResolvedIntegerLiteralConstructs shape.bodyContext (.decimal "7")
            literalResolution (.word (Word.ofNatModulo 7)) := .word (numericLiteralValue?_sound rfl) proves
        exact ⟨congrArg _ (constructed.functional expected), rfl⟩
    | generalizedLocal contains otherForm _ _ _ _ _ _ _ =>
      exact False.elim (nonlocal _ _ (sameNode _ contains ▸ otherForm))
  | @fault _ _ reason failed =>
    have rawFault : Dynamic.ExpressionFormFaults (Program.ofChecked fixture.packet.compiled.sourceProgram)
        shape.bodyContext [] (source fixture.packet.named) environment before
        fixture.graph.literal.form fixture.graph.literal.requirements fixture.graph.literal.coercions reason after := by
      cases failed with
      | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent (lookupExpression?_sound found))
      | form contains failed => exact sameNode _ contains ▸ failed
      | coercion contains _ failed =>
        have same := sameNode _ contains
        subst same
        rw [fixture.graph.literalCoercions] at failed
        cases failed
      | generalizedLocalRequirement contains otherForm _ _ _ _ _ _ _
      | generalizedLocalCoercion contains otherForm _ _ _ _ _ _ _ =>
        exact False.elim (nonlocal _ _ (sameNode _ contains ▸ otherForm))
    rw [fixture.graph.literalForm] at rawFault
    cases rawFault with
    | integerRequirement _ unavailable => exact False.elim (safe unavailable)

/-- The actual explicit return admits only the selected Word result; the
finite Source statement inversions preserve the parameter heap exactly. -/
private theorem return_outcome {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome} {size : Nat}
    (trace : RecursiveNamedLoopContracts.ExecutesAt size true (Program.ofChecked fixture.packet.compiled.sourceProgram)
      shape.bodyContext [] (source fixture.packet.named) environment before
      [statementId fixture.packet 2] finalContext outcome after) :
    outcome = .returned (.word (Word.ofNatModulo 7)) ∧ after = before := by
  have unique := fixture.runtime.source_runtime.graph.nodeOccurrencesUnique
  have found := lookupStatement?_sound fixture.graph.returnedFound
  have inverted := RecursiveNamedStatementSourceBounds.cons_inv unique found
    (by intro _ _ expression; rw [fixture.graph.returnedForm]; simp) trace
  cases inverted with
  | next head _ _ _ =>
    have returned := RecursiveNamedStatementSourceBounds.return_value unique found fixture.graph.returnedForm head
    obtain ⟨_sameContext, child, value, impossible, _evaluated, _strict⟩ := returned
    cases impossible
  | terminal head _ _ =>
    obtain ⟨_sameContext, child, value, result, evaluated, _strict⟩ :=
      RecursiveNamedStatementSourceBounds.return_value unique found fixture.graph.returnedForm head
    obtain ⟨sameValue, sameHeap⟩ := literal_outcome fixture shape (.value evaluated.sound)
    exact ⟨result.trans (congrArg Dynamic.ControlOutcome.returned (Dynamic.ExpressionOutcome.value.inj sameValue)), sameHeap⟩
  | fault head _ =>
    obtain ⟨child, failed, _strict⟩ := RecursiveNamedStatementSourceBounds.return_fault unique found fixture.graph.returnedForm head
    have impossible := (literal_outcome fixture shape (.fault failed.sound)).1
    cases impossible

include atHeader shape in
/-- Real call inversion exposes the copies of the captured cells and the
original parameter allocation. Their heap preservation and the literal return
prove the final deep Source heap locally. -/
theorem call_heap {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome} {size : Nat}
    (heapTyped : Dynamic.HeapWellTyped (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) before)
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) size
      context evidence (receipt.formation.function []).evidence before (.closure (receipt.formation.function []))
      [SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argumentValue] outcome after) :
    outcome = .value (.word (Word.ofNatModulo 7)) ∧
    Dynamic.HeapWellTyped (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) after := by
  have parameters := (SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader receipt []).1
  have arity : (receipt.formation.function []).parameters.length =
      [SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argumentValue].length := by
    rw [parameters, shape.parameters]
    rfl
  obtain ⟨types, bodyContext, entry, copied, environment, bound, extended, copy, allocated, body⟩ :=
    FunctionCallBody.Outcome.trace arity trace.sound
  have entryContext : bodyContext = shape.bodyContext := by
    have original : MonoBindersExtend (receipt.formation.function []).source.owner
        (receipt.formation.function []).context (receipt.formation.function []).parameters [parameterType]
        shape.bodyContext := by
      change MonoBindersExtend (source caller.named).owner (runtimeContext fixture.packet) _ _ _
      simpa only [parameters, atHeader.named] using shape.parameters_extend
    have sameTypes : types = [parameterType] := extended.bodyTypes_eq.symm.trans original.bodyTypes_eq
    subst types
    exact extended.functional original
  have valuesTyped : Dynamic.ValuesHaveTypes (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
      copied [SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argumentValue]
      ((receipt.formation.function []).parameters.map (fun binder => binder.scheme.body)) := by
    rw [parameters, shape.parameters]
    simpa only [List.map_cons, List.map_nil, shape.scheme, TypeSystem.Scheme.mono] using
      SourceCoreChosenOrdinaryAcceptedArgumentAdmission.arguments_typed
        (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) copied
  have boundTyped := Dynamic.BindersAllocate.preservesHeapTyping (heapTyped.copy copy) valuesTyped allocated
  have bodyShape := (SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader receipt []).2
  have expected : outcome = .value (.word (Word.ofNatModulo 7)) ∧ after = bound := by
    cases body with
    | @returned finalContext result _ executed =>
      obtain ⟨bodySize, executed⟩ := SourceExecutionSize.FunctionStatementsExecute.has_size executed
      change SourceExecutionSize.FunctionStatementsExecute _ bodySize bodyContext [] (source caller.named)
        environment bound _ finalContext _ after at executed
      rw [atHeader.named] at executed
      have actual : RecursiveNamedLoopContracts.ExecutesAt bodySize true (Program.ofChecked fixture.packet.compiled.sourceProgram)
          shape.bodyContext [] (source fixture.packet.named) environment bound [statementId fixture.packet 2]
          finalContext (.returned result) after := by
        simpa only [RecursiveNamedLoopContracts.ExecutesAt, entryContext, bodyShape.2, atHeader.named] using (RecursiveNamedCallBounds.FunctionOutcome.control executed)
      have same := return_outcome fixture shape actual
      exact ⟨congrArg Dynamic.ExpressionOutcome.value (Dynamic.ControlOutcome.returned.inj same.1), same.2⟩
    | unit resultUnit _ =>
      rw [bodyShape.1] at resultUnit
      cases resultUnit
    | @fault finalContext reason _ failed =>
      obtain ⟨bodySize, failed⟩ := SourceExecutionSize.FunctionStatementsFault.has_size failed
      change SourceExecutionSize.FunctionStatementsFault _ bodySize bodyContext [] (source caller.named)
        environment bound _ finalContext _ after at failed
      rw [atHeader.named] at failed
      have actual : RecursiveNamedLoopContracts.ExecutesAt bodySize true (Program.ofChecked fixture.packet.compiled.sourceProgram)
          shape.bodyContext [] (source fixture.packet.named) environment bound [statementId fixture.packet 2]
          finalContext (.fault reason) after := by
        simpa only [RecursiveNamedLoopContracts.ExecutesAt, entryContext, bodyShape.2, atHeader.named] using (RecursiveNamedCallBounds.FunctionOutcome.fault failed)
      have impossible := (return_outcome fixture shape actual).1
      cases impossible
    | @escaped finalContext control _ executed escape =>
      obtain ⟨bodySize, executed⟩ := SourceExecutionSize.FunctionStatementsExecute.has_size executed
      change SourceExecutionSize.FunctionStatementsExecute _ bodySize bodyContext [] (source caller.named)
        environment bound _ finalContext _ after at executed
      rw [atHeader.named] at executed
      have actual : RecursiveNamedLoopContracts.ExecutesAt bodySize true (Program.ofChecked fixture.packet.compiled.sourceProgram)
          shape.bodyContext [] (source fixture.packet.named) environment bound [statementId fixture.packet 2]
          finalContext control after := by
        simpa only [RecursiveNamedLoopContracts.ExecutesAt, entryContext, bodyShape.2, atHeader.named] using (RecursiveNamedCallBounds.FunctionOutcome.control executed)
      have same := (return_outcome fixture shape actual).1
      rcases escape with ⟨_, escaped⟩ | ⟨_, escaped⟩ <;> rw [same] at escaped <;> cases escaped
  exact ⟨expected.1, expected.2 ▸ boundTyped⟩


/-- The actual three Source children compose by the original indirect-parent
constructors. Physical argument count follows from this fixture's real trace. -/
theorem parent_source {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before calleeHeap middle after : Dynamic.Heap} {arguments : List Dynamic.Value}
    {outcome : Dynamic.ExpressionOutcome} {calleeSize argumentsSize callSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      calleeSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
      (source fixture.packet.named) environment before (expressionId fixture.packet 9)
      (.closure (receipt.formation.function [])) calleeHeap)
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked fixture.packet.compiled.sourceProgram)
      argumentsSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
      (source fixture.packet.named) environment calleeHeap [expressionId fixture.packet 6] arguments middle)
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) callSize
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
      (receipt.formation.function []).evidence middle (.closure (receipt.formation.function [])) arguments outcome after) :
    ∃ size, RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) size
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
      (source fixture.packet.named) environment before (expressionId fixture.packet 5) outcome after := by
  have actualArity : arguments.length = indirectMetadata.argumentCount := by
    rw [(arguments_at fixture argumentsTrace).1]
    rfl
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack arguments
  cases called with
  | @value result _ applied =>
    refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize,
      SourceExecutionSize.stepSize [], callSize], SourceExecutionSize.stepSize []],
      .value (.intro (raw := result) (middle := after) (lookupExpression?_sound fixture.graph.parentFound) ?_ ?_)⟩
    · rw [fixture.graph.parentForm]
      refine .indirectCall ?_ calleeTrace argumentsTrace packing (.nil) packing rfl actualArity applied
      simp [fixture.graph.parentRequirements, fixture.graph.parentCoercions, indirectMetadata, coercionRequirementIds]
    · rw [fixture.graph.parentCoercions]
      exact .nil
  | fault failed =>
    refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize,
      SourceExecutionSize.stepSize [], callSize]], .fault (.form (lookupExpression?_sound fixture.graph.parentFound) ?_)⟩
    rw [fixture.graph.parentForm]
    exact .indirectApply calleeTrace argumentsTrace packing (.nil) packing rfl actualArity failed

section Current
universe u
variable {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    {mapping : LocationMap} {world : StoreTyping} {actualEnvironment : Environment}
    (captured : Captures fixture.packet.compiled.indexed mapping world (initialScope fixture.packet)
      (receipt.formation.function []).captured actualEnvironment)
    (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
      (values := .initial fixture.packet.compiled.compatible.checked) caller)
    (history : History (receipt.formation.code []))
    (origin : SourceOrigin (receipt.formation.support []) history)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := fixture.packet.compiled.indexed)
      (values := .initial fixture.packet.compiled.compatible.checked)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      headers owner.key.locations 1 (initialScope fixture.packet) captured.canonical owner.key.frameLocation)
    {arguments : List Dynamic.Value} {payloads : List Value}
    {calleeHeap middle : Dynamic.Heap} {argumentStore : Store}
    {callerScope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    (argumentState : callerProtocol.State ⟨callerScope, mapping, world, middle, argumentStore, canonical⟩)
    (admitted : Admission bridge (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) argumentState)
    (heaps : CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry functions
      mapping world middle argumentStore)
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
      mapping world (receipt.formation.code []).receipt.loweredParameters arguments payloads)
    (reference : captured.canonical[(receipt.formation.code []).referenceIndex]? =
      some (.cellRef fixture.packet.compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
    {argumentSize : Nat}
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked fixture.packet.compiled.sourceProgram)
      argumentSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
      (source fixture.packet.named) environment calleeHeap [expressionId fixture.packet 6] arguments middle)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {compilerFuel : Nat}
    {compilerContext : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
    {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (compiler : CallableIndirectCallCertificates.Receipt policy body compilerFuel compilerContext
      (source fixture.packet.named) scope (expressionId fixture.packet 5) (expressionId fixture.packet 9)
      [expressionId fixture.packet 6] metadata reasonAt lowered)
    {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
    {sidecar : SourceCoreStageContracts.Sidecar} {calleeNative : Value} {actual : Environment}
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call
      [expressionId fixture.packet 6] (.closure (receipt.formation.function [])) calleeNative)
    (sameNative : calleeNative = CallableIndexedLambdaValues.value (receipt.formation.code [])
      captured.embedding history.native actualEnvironment)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site
      (expressionId fixture.packet 9) [expressionId fixture.packet 6] metadata compiler.original dispatch.row)

/-- The actual application result retains its original whole-pool transition
and a genuine successful Source admission at the same returned caller. -/
def ReturnedAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt (registry := registry) (faults := faults)
    (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt [] captured prefixContext)
    (receipt.formation.code []) functions (bridge.pool argumentState) outcome after value finalStore finalMap finalWorld ∧
  ∃ returned : callerProtocol.State ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates argumentState returned ∧
    PostAdmission bridge (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) wordType outcome returned

include atHeader shape admitted argumentsTrace in
/-- The real call trace authenticates the final raw heap. The Carrier lift
returns its existing pool and does not run another physical restoration. -/
private theorem result_admission {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) size
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
      (receipt.formation.function []).evidence middle (.closure (receipt.formation.function [])) arguments outcome after)
    (result : CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt (registry := registry) (faults := faults)
      (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt [] captured prefixContext)
      (receipt.formation.code []) functions (bridge.pool argumentState) outcome after value finalStore finalMap finalWorld) :
    ReturnedAt (registry := registry) (faults := faults) fixture receipt bridge functions captured prefixContext argumentState outcome after value finalStore finalMap finalWorld := by
  have actualCalled : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) size
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
      (receipt.formation.function []).evidence middle (.closure (receipt.formation.function []))
      [SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argumentValue] outcome after := by
    simpa only [(arguments_at fixture argumentsTrace).1] using called
  have sourcePost := call_heap fixture atHeader shape receipt admitted.heap actualCalled
  have kept := result
  obtain ⟨_represented, _heaps, maps, worlds, frame, metadata, reached, related⟩ := result
  obtain ⟨returned, _samePool, returnedRelated⟩ := bridge.restore argumentState reached maps worlds frame metadata related
  refine ⟨kept, returned, returnedRelated, ?_⟩
  refine ⟨CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
    (bridge.pool argumentState) (bridge.pool returned) admitted.rows frame, ?_⟩
  intro sourceValue isValue
  have sameValue := Dynamic.ExpressionOutcome.value.inj (isValue.symm.trans sourcePost.1)
  cases sameValue
  exact ⟨.word _, sourcePost.2⟩

include atHeader shape typing chosen origin observed admitted heaps represented reference argumentsTrace sameNative selected in
/-- The real Source argument trace constructs raw typing at this argument
state. The literal application and original accepted fourth bind run once. -/
theorem application_preserves (budget : Nat)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) size
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
      (receipt.formation.function []).evidence middle (.closure (receipt.formation.function [])) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: .unit :: calleeNative :: actual) argumentStore
        (LanguageResult.bind compiler.resultType
          (CallableContract.dispatch prepared.site.gates .beforeApplication native.diagnostics.unknown (.second (.var 2)))
          (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧
      ReturnedAt (registry := registry) (faults := faults) fixture receipt bridge functions captured prefixContext argumentState
        outcome after value finalStore finalMap finalWorld := by
  have passed := (SourceCoreChosenOrdinaryAcceptedLiteralCallGuard.accepted_at_selected
    fixture shape atHeader receipt dispatch selected native.diagnostics.unknown).fourth
  have rawTyped : Dynamic.ValuesHaveTypes (runtimeContext fixture.packet) middle arguments [parameterType] := by
    rw [(arguments_at fixture argumentsTrace).1]
    exact SourceCoreChosenOrdinaryAcceptedArgumentAdmission.arguments_typed _ _
  have beforeTyped : Dynamic.HeapWellTyped (runtimeContext fixture.packet) middle :=
    (Dynamic.HeapWellTyped.iff_of_binderExtends typing.extended).mpr admitted.heap
  obtain ⟨value, finalStore, finalMap, finalWorld, application, result⟩ :=
    SourceCoreChosenOrdinaryAcceptedLiteralInvocation.application_preserves fixture atHeader receipt shape root chosen
      functions owner captured prefixContext history origin observed (bridge.pool argumentState) beforeTyped rawTyped
      admitted.rows represented heaps reference budget called within
  have read : Evaluates (DataPatternValues.packValues payloads :: .unit :: calleeNative :: actual) argumentStore
      (.second (.var 2)) (.word dispatch.contract) argumentStore :=
    .second (.var (by simpa only [List.getElem?_cons_succ, List.getElem?_cons_zero] using congrArg some dispatch.shape))
  have gate := prepared.site.dispatch_known .beforeApplication native.diagnostics.unknown
    dispatch.contract dispatch.row dispatch.found read
  rw [SourceCoreCallableContracts.reason_accepted dispatch.row prepared.site.reasonAt .beforeApplication passed] at gate
  rw [← sameNative] at application
  exact ⟨value, finalStore, finalMap, finalWorld,
    LanguageResult.bind_success compiler.resultType gate
      (CallableIndexedOwnedStoredApplicationProjection.evaluates_from_payload application),
    result_admission fixture atHeader shape receipt bridge functions captured prefixContext argumentState admitted
      argumentsTrace called result⟩

include atHeader shape typing chosen origin observed admitted heaps represented reference argumentsTrace sameNative selected in
/-- Genuine fourth-bind completion supplies its strict application child. The
selected literal continuation derives the body internally at this exact state. -/
theorem application_reflects (budget : Nat)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: .unit :: calleeNative :: actual) argumentStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication native.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) sourceSize
        (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
        (receipt.formation.function []).evidence middle (.closure (receipt.formation.function [])) arguments outcome after ∧
      ReturnedAt (registry := registry) (faults := faults) fixture receipt bridge functions captured prefixContext argumentState
        outcome after value finalStore finalMap finalWorld := by
  have passed := (SourceCoreChosenOrdinaryAcceptedLiteralCallGuard.accepted_at_selected
    fixture shape atHeader receipt dispatch selected native.diagnostics.unknown).fourth
  have rawTyped : Dynamic.ValuesHaveTypes (runtimeContext fixture.packet) middle arguments [parameterType] := by
    rw [(arguments_at fixture argumentsTrace).1]
    exact SourceCoreChosenOrdinaryAcceptedArgumentAdmission.arguments_typed _ _
  have beforeTyped : Dynamic.HeapWellTyped (runtimeContext fixture.packet) middle :=
    (Dynamic.HeapWellTyped.iff_of_binderExtends typing.extended).mpr admitted.heap
  have read : Evaluates (DataPatternValues.packValues payloads :: .unit :: calleeNative :: actual) argumentStore
      (.second (.var 2)) (.word dispatch.contract) argumentStore :=
    .second (.var (by simpa only [List.getElem?_cons_succ, List.getElem?_cons_zero] using congrArg some dispatch.shape))
  have gate := prepared.site.dispatch_known .beforeApplication native.diagnostics.unknown
    dispatch.contract dispatch.row dispatch.found read
  rw [SourceCoreCallableContracts.reason_accepted dispatch.row prepared.site.reasonAt .beforeApplication passed] at gate
  cases CallableIndirectCallBounds.bind_completed completed within with
  | failed failed _ =>
    have same := (evaluation_deterministic failed.sound gate).1
    cases same
  | continued acceptedGate applicationTrace _gateStrict applicationStrict =>
    obtain ⟨same, stores⟩ := evaluation_deterministic acceptedGate.sound gate
    cases same
    subst stores
    have payload := CallableIndexedOwnedStoredApplicationProjection.to_payload applicationTrace
    rw [sameNative] at payload
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, called, result⟩ :=
      SourceCoreChosenOrdinaryAcceptedLiteralInvocation.application_reflects fixture atHeader receipt shape root chosen
        functions owner captured prefixContext history origin observed (bridge.pool argumentState) beforeTyped rawTyped
        admitted.rows represented heaps reference budget payload (Nat.le_of_lt applicationStrict)
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, called,
      result_admission fixture atHeader shape receipt bridge functions captured prefixContext argumentState admitted
        argumentsTrace called result⟩

end Current

section SuccessStep
universe u
variable {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
    (profile : fixture.packet.compiled.compatible.checked.catalog.callableContracts = true)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    {calleeMap : LocationMap} {calleeWorld : StoreTyping} {actualEnvironment : Environment}
    (captured : Captures fixture.packet.compiled.indexed calleeMap calleeWorld (initialScope fixture.packet)
      (receipt.formation.function []).captured actualEnvironment)
    (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
      (values := .initial fixture.packet.compiled.compatible.checked) caller)
    (history : History (receipt.formation.code []))
    (origin : SourceOrigin (receipt.formation.support []) history)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := fixture.packet.compiled.indexed)
      (values := .initial fixture.packet.compiled.compatible.checked)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      headers owner.key.locations 1 (initialScope fixture.packet) captured.canonical owner.key.frameLocation)
    (reference : captured.canonical[(receipt.formation.code []).referenceIndex]? =
      some (.cellRef fixture.packet.compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {compilerFuel : Nat}
    {compilerContext : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
    {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (compiler : CallableIndirectCallCertificates.Receipt policy body compilerFuel compilerContext
      (source fixture.packet.named) scope (expressionId fixture.packet 5) (expressionId fixture.packet 9)
      [expressionId fixture.packet 6] metadata reasonAt lowered)
    {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
    {sidecar : SourceCoreStageContracts.Sidecar} {calleeNative : Value} {actual : Environment} {ξ : Renaming}
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call
      [expressionId fixture.packet 6] (.closure (receipt.formation.function [])) calleeNative)
    (sameNative : calleeNative = CallableIndexedLambdaValues.value (receipt.formation.code [])
      captured.embedding history.native actualEnvironment)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site
      (expressionId fixture.packet 9) [expressionId fixture.packet 6] metadata compiler.original dispatch.row)
    (nativeBundle : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
      (receipt.formation.code []).receipt.parameterCore)
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {firstMap : LocationMap} {firstWorld : StoreTyping} {before calleeHeap : Dynamic.Heap}
    {firstStore calleeStore : Store} {canonical : Environment}
    (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)

include atHeader shape typing chosen profile origin observed reference selected sameNative nativeBundle in
/-- The original whole successful prefix and fourth bind remain beside the
independent Source call and actual returned admission. No argument or body
meaning callback is supplied; the same step's values construct the bundle. -/
theorem reflects_success_step (budget : Nat) {value : Value} {finalStore : Store} {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      calleeSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
      (source fixture.packet.named) environment before (expressionId fixture.packet 9)
      (.closure (receipt.formation.function [])) calleeHeap)
    (original : CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
      (evidence := evidence) (environment := environment) (actual := actual) (ξ := ξ)
      (sourceTypes := [parameterType]) (calleeHeap := calleeHeap) (calleeNative := calleeNative)
      (calleeStore := calleeStore) bridge functions compiler prepared first budget value finalStore)
    (step : CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
      (evidence := evidence) (environment := environment) (actual := actual) (ξ := ξ)
      (sourceTypes := [parameterType]) (calleeHeap := calleeHeap) (calleeNative := calleeNative)
      (calleeStore := calleeStore) (calleeMap := calleeMap) (calleeWorld := calleeWorld)
      bridge functions compiler prepared first budget value finalStore)
    (passed : CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore) :
    CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
      (evidence := evidence) (environment := environment) (actual := actual) (ξ := ξ)
      (sourceTypes := [parameterType]) (calleeHeap := calleeHeap) (calleeNative := calleeNative)
      (calleeStore := calleeStore) bridge functions compiler prepared first budget value finalStore ∧
    CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
      (evidence := evidence) (environment := environment) (actual := actual) (ξ := ξ)
      (sourceTypes := [parameterType]) (calleeHeap := calleeHeap) (calleeNative := calleeNative)
      (calleeStore := calleeStore) (calleeMap := calleeMap) (calleeWorld := calleeWorld)
      bridge functions compiler prepared first budget value finalStore ∧
    CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore ∧
    ∃ argumentsSize sources payloads middle argumentStore middleMap middleWorld,
    ∃ (stepMaps : LocationMap.Extends calleeMap middleMap) (stepWorlds : WorldExtends calleeWorld middleWorld)
      (argumentState : callerProtocol.State ⟨scope, middleMap, middleWorld, middle, argumentStore, canonical⟩),
      callerProtocol.Relates first argumentState ∧
      Admission bridge (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) argumentState ∧
      DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
        middleMap middleWorld [parameterType] (compiler.codes.map (·.type)) sources payloads ∧
      SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked fixture.packet.compiled.sourceProgram) argumentsSize
        (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
        (source fixture.packet.named) environment calleeHeap [expressionId fixture.packet 6] sources middle ∧
      ∃ callSize outcome after finalMap finalWorld,
        RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) callSize
          (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
          (receipt.formation.function []).evidence middle (.closure (receipt.formation.function [])) sources outcome after ∧
        ∃ parentSize, RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
          parentSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
          (source fixture.packet.named) environment before (expressionId fixture.packet 5) outcome after ∧
        ReturnedAt (registry := registry) (faults := faults) fixture receipt bridge functions
          (captured.extend stepMaps stepWorlds) prefixContext argumentState outcome after value finalStore finalMap finalWorld := by
  refine ⟨original, step, passed, ?_⟩
  obtain ⟨nativeSize, argumentsSize, arguments, payloads, middle, argumentStore, middleMap, middleWorld,
    _argumentsNative, _argumentsStrict, argumentsTrace, values, argumentHeaps, stepMaps, stepWorlds, _stepFrame, _stepMetadata,
    _maps, _worlds, _frame, _metadata, ⟨argumentState, related, admitted⟩,
    remainingSize, remaining, remainingStrict⟩ := step
  let current := captured.extend stepMaps stepWorlds
  have rawBundle : TypeSystem.Ty.productMany [parameterType] =
      TypeSystem.Ty.productMany ((receipt.formation.function []).parameters.map (fun binder => binder.scheme.body)) := by
    rw [(SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader receipt []).1, shape.parameters]
    simp only [List.map_cons, List.map_nil, shape.scheme, TypeSystem.Scheme.mono]
  have count : (compiler.codes.map (·.type)).length = (receipt.formation.function []).parameters.length := by
    have physical := SourceCoreChosenOrdinaryAcceptedLiteralCallGuard.physical_arity fixture shape atHeader receipt
    simpa only [List.length_map] using compiler.ordered_children.1.symm.trans physical.symm
  have actualArguments := CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.arguments_of_bundles
    (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt [] current prefixContext)
    (receipt.formation.code []) (receipt.formation.support []) (receipt.formation.prepared [])
    functions profile values (count.symm.trans values.length.1) rawBundle nativeBundle
  obtain ⟨callSize, outcome, after, finalMap, finalWorld, called, result⟩ :=
    application_reflects (registry := registry) (faults := faults)
      (atHeader := atHeader) (shape := shape) (typing := typing) (receipt := receipt) (root := root) (chosen := chosen)
      (bridge := bridge) (functions := functions) (owner := owner) (captured := current)
      (prefixContext := prefixContext) (history := history) (origin := origin) (observed := observed)
      (argumentState := argumentState) (admitted := admitted) (heaps := argumentHeaps)
      (represented := actualArguments) (reference := reference) (argumentsTrace := argumentsTrace)
      (compiler := compiler) (prepared := prepared) (dispatch := dispatch) (sameNative := sameNative)
      (selected := selected) fixture budget remaining (Nat.le_of_lt remainingStrict)
  obtain ⟨parentSize, sourceParent⟩ := parent_source fixture receipt calleeTrace argumentsTrace called
  exact ⟨argumentsSize, arguments, payloads, middle, argumentStore, middleMap, middleWorld,
    stepMaps, stepWorlds, argumentState, related, admitted, values, argumentsTrace,
    callSize, outcome, after, finalMap, finalWorld, called, parentSize, sourceParent, result⟩

end SuccessStep
end Tests.SourceCoreChosenOrdinaryAcceptedLiteralStoredApplication
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedPairArgumentBounds
/-! The actual accepted parent supplies its ordered tuple and numeric child
receipts at the original remaining compiler budgets. The original admitted
sequence and tuple proofs consume those children at their actual caller state. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedPairArgumentBounds
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreChosenOrdinaryAcceptedFixture CallableIndexedNamedGeneration
open CallableIndexedOwnedLiteralReturnSiteShells CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission

variable (fixture : AcceptedFixture)

def parentScope : SourceCoreLocalCell.Scope :=
  (fixture.graph.binder.id, fixture.calls.payload) :: initialScope fixture.packet

/-- Only the two retained numeric argument occurrences belong to this family. -/
def Child : GenericExpressionMeaning.Certificate := fun _ id code =>
  (id = expressionId fixture.packet 7 ∨ id = expressionId fixture.packet 8) ∧
    CompatibleExpressionLiteralRuntime.Certificate
      (context fixture.packet.compiled.indexed fixture.packet.named).solvedRequirements
      (source fixture.packet.named) id code

variable {compilation : Compilation fixture.packet.compiled.indexed fixture.packet.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : LiteralRootReceipt (compiled := fixture.packet.compiled) fixture.packet.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
    498 (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1)
    ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
    fixture.calls.initializer)

/-- The parent-selected tuple and both ordered children keep their actual
acceptance equations. Neither Source nor native execution is a field. -/
structure PairReceipt where
  left : SourceCoreBasic.LoweredExpr
  right : SourceCoreBasic.LoweredExpr
  tuple : SourceCoreBasic.LoweredExpr
  tupleAccepted : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
    497 (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
    (parentScope fixture) (expressionId fixture.packet 6)
    ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key) = .ok tuple
  leftAccepted : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
    496 (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
    (parentScope fixture) (expressionId fixture.packet 7)
    ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key) = .ok left
  rightAccepted : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
    496 (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
    (parentScope fixture) (expressionId fixture.packet 8)
    ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key) = .ok right
  packed : tuple = SourceCoreCalls.packArguments [left, right]
  metadata : CompatibleExpressionPrimitives.Metadata fixture.packet.compiled.compatible.checked
    (source fixture.packet.named) (expressionId fixture.packet 6) fixture.graph.argument tuple.type
  leftCertified : Child fixture (parentScope fixture) (expressionId fixture.packet 7) left
  rightCertified : Child fixture (parentScope fixture) (expressionId fixture.packet 8) right

private theorem empty_owned (node : ExpressionNode) (requirements : node.requirements = [])
    (coercions : node.coercions = []) : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
  unfold SourceCompilationPlan.ordinaryOwnedRequirements?
  rw [requirements, coercions]
  rfl

include root in
/-- One actual parent acceptance exposes tuple497 and literal496. The original
indirect and tuple compiler receipts retain their original Source order. -/
theorem compiler_receipt
    (parentAccepted : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
      498 (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
      (parentScope fixture) (expressionId fixture.packet 5)
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key) = .ok fixture.calls.parent) :
    Nonempty (PairReceipt fixture root) := by
  have parentPolicy := indirect_policy root.root (scope := parentScope fixture)
    (reasonAt := (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
    fixture.graph.parentFound fixture.graph.parentForm fixture.graph.parentRequirements
    fixture.graph.parentCoercions rfl fixture.calls.parentOrdinary
  obtain ⟨parent⟩ := CallableIndirectCallCertificates.of_functions fixture.graph.parentFound fixture.graph.parentForm
    parentPolicy.special (parentPolicy.read.trans fixture.parentRows.parentRead) fixture.graph.parentForm parentAccepted
  cases tupleAction : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
      497 (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
      (parentScope fixture) (expressionId fixture.packet 6)
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key) with
  | error error =>
      have accepted := parent.argumentsAccepted
      simp [tupleAction, List.mapM_cons, bind, Except.bind] at accepted
  | ok tuple =>
    have tuplePolicy := SourceCoreChosenOrdinaryAcceptedStaticInventory.ordinary_policy root.root
      (childScope := parentScope fixture) fixture.graph.argumentFound (.inr (.inl ⟨_, fixture.graph.argumentForm⟩))
      (empty_owned fixture.graph.argument fixture.parentRows.argumentRequirements fixture.parentRows.argumentCoercions)
      fixture.parentRows.argumentCoercions (.inl fixture.parentRows.argumentRequirements) fixture.parentRows.argumentOrdinary
    obtain ⟨codes, children, packed, metadata⟩ := CompatibleExpressionTuples.of_functions
      (values := .initial fixture.packet.compiled.compatible.checked) fixture.graph.argumentFound fixture.graph.argumentForm
      tuplePolicy.special tuplePolicy.read root.leaf tupleAction
    cases leftAction : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
      496 (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
      (parentScope fixture) (expressionId fixture.packet 7)
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key) with
    | error error => simp [List.mapM_cons, leftAction, bind, Except.bind] at children
    | ok left =>
      cases rightAction : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
        496 (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
        (parentScope fixture) (expressionId fixture.packet 8)
        ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key) with
      | error error => simp [List.mapM_cons, leftAction, rightAction, bind, Except.bind] at children
      | ok right =>
        simp only [List.mapM_cons, List.mapM_nil, leftAction, rightAction, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at children
        subst codes
        have leftPolicy := SourceCoreChosenOrdinaryAcceptedStaticInventory.ordinary_policy root.root
          (childScope := parentScope fixture) fixture.parentRows.leftFound (.inr (.inr ⟨_, _, fixture.parentRows.leftForm⟩))
          fixture.parentRows.leftOwned fixture.parentRows.leftCoercions (.inr ⟨_, _, fixture.parentRows.leftForm⟩) fixture.parentRows.leftOrdinary
        have rightPolicy := SourceCoreChosenOrdinaryAcceptedStaticInventory.ordinary_policy root.root
          (childScope := parentScope fixture) fixture.parentRows.rightFound (.inr (.inr ⟨_, _, fixture.parentRows.rightForm⟩))
          fixture.parentRows.rightOwned fixture.parentRows.rightCoercions (.inr ⟨_, _, fixture.parentRows.rightForm⟩) fixture.parentRows.rightOrdinary
        have leftCertified := CompatibleExpressionLiteralRuntime.of_functions (values := .initial fixture.packet.compiled.compatible.checked)
          fixture.parentRows.leftFound (by rw [fixture.parentRows.leftForm]; exact .integer _ _)
          (by intro form; rw [fixture.parentRows.leftForm] at form; cases form)
          leftPolicy.special leftPolicy.read root.leaf leftAction
        have rightCertified := CompatibleExpressionLiteralRuntime.of_functions (values := .initial fixture.packet.compiled.compatible.checked)
          fixture.parentRows.rightFound (by rw [fixture.parentRows.rightForm]; exact .integer _ _)
          (by intro form; rw [fixture.parentRows.rightForm] at form; cases form)
          rightPolicy.special rightPolicy.read root.leaf rightAction
        exact ⟨⟨left, right, tuple, tupleAction, leftAction, rightAction, packed,
          packed.symm ▸ metadata, ⟨.inl rfl, leftCertified⟩, ⟨.inr rfl, rightCertified⟩⟩⟩

private theorem child_fields (metadata : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (allowed : id = expressionId fixture.packet 7 ∨ id = expressionId fixture.packet 8)
    (found : (source fixture.packet.named).lookupExpression? id = some node) :
    node.type = .word ∧ node.coercions = [] := by
  rcases allowed with rfl | rfl
  · have same := Option.some.inj (found.symm.trans fixture.parentRows.leftFound)
    subst node
    exact ⟨metadata.leftType, fixture.parentRows.leftCoercions⟩
  · have same := Option.some.inj (found.symm.trans fixture.parentRows.rightFound)
    subst node
    exact ⟨metadata.rightType, fixture.parentRows.rightCoercions⟩

private theorem child_outcome {id : ExpressionId}
    (allowed : id = expressionId fixture.packet 7 ∨ id = expressionId fixture.packet 8)
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {value : Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (first : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
      environment before id (.value value) before)
    (second : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
      environment before id outcome after) : outcome = .value value ∧ after = before := by
  rcases allowed with rfl | rfl
  · have raw := SourceCoreChosenOrdinaryAcceptedArgumentAdmission.left_outcome fixture first
    have actual := SourceCoreChosenOrdinaryAcceptedArgumentAdmission.left_outcome fixture second
    exact ⟨actual.1.trans raw.1.symm, actual.2⟩
  · have raw := SourceCoreChosenOrdinaryAcceptedArgumentAdmission.right_outcome fixture first
    have actual := SourceCoreChosenOrdinaryAcceptedArgumentAdmission.right_outcome fixture second
    exact ⟨actual.1.trans raw.1.symm, actual.2⟩

private theorem literal_word_type {solved : List SolvedRequirement} {node : ExpressionNode} {type : Ty} {code : Expr}
    (literal : CompatibleExpressionLiterals.Literal solved node type code) (wordType : node.type = .word) : type = .word := by
  cases literal with
  | unit _ typed _ _ | bool _ _ typed _ _ => cases typed.symm.trans wordType
  | word => rfl
  | resolvedWord => rfl
  | resolvedInteger _ metadata => cases metadata.nodeType.symm.trans wordType

private theorem word_typed {solved : List SolvedRequirement} {node : ExpressionNode} {code : Expr}
    (literal : CompatibleExpressionLiterals.Literal solved node .word code)
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap} {value : Dynamic.Value}
    (raw : Dynamic.ExpressionFormEvaluates program context evidence source environment heap
      node.form node.requirements node.coercions value heap) : Dynamic.ValueHasType context heap value .word := by
  cases literal with
  | word _ form _ _ _ _ =>
    rw [form] at raw
    cases raw with | literal _ constructed => cases constructed; exact .word _
  | resolvedWord form metadata =>
    rw [form] at raw
    cases raw with | integerLiteral _ constructed =>
      cases constructed with
      | word => exact .word _
      | integer => cases metadata.targetType

section Admitted
universe u
variable {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (metadata : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
    (evidence : Dynamic.EvidenceEnvironment)

include metadata in
/-- The real numeric row produces its original pure tuple and current Word
admission. No expression meaning or induction hypothesis is supplied. -/
theorem literal_preserves (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
      (Child fixture) faults size := by
  intro scope id code certified node found _sourceTyped mapping world administrative environment canonical native
    actualContext before store ξ outcome after _environments heaps _locals _agrees _typed initial admitted trace
  obtain ⟨allowed, other, otherFound, literal, selected⟩ := certified
  have same := Option.some.inj (otherFound.symm.trans found)
  subst other
  have fields := child_fields fixture metadata allowed found
  have nativeWord := literal_word_type literal fields.1
  rw [nativeWord] at literal
  have numeric := selected.evidence (context := SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
    rfl (numeric_runtime_ledger fixture.runtime.rows) evidence
  obtain ⟨sourceValue, coreValue, raw, related, evaluated⟩ := literal.evaluates_with_evidence (registry := registry)
    functions (Program.ofChecked fixture.packet.compiled.sourceProgram)
    (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence numeric
    _ environment before mapping world native store ξ
  have sourceTrace : Dynamic.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
      environment before id sourceValue before := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found) raw
    rw [fields.2]
    exact .nil
  obtain ⟨sameOutcome, sameHeap⟩ := child_outcome fixture allowed (.value sourceTrace) trace.sound
  subst outcome
  subst after
  refine ⟨.inRight .word coreValue, store, mapping, world, evaluated,
    .value (by simpa only [CompatibleAmbientHeap.payloadModel, nativeWord] using related), heaps,
    .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial, admitted.rows, ?_⟩
  intro value same
  cases same
  rw [fields.1]
  exact ⟨word_typed literal raw, admitted.heap⟩

include metadata in
/-- Native determinism aligns the same pure literal output. Its reconstructed
Source grade is independent of the actual native child size. -/
theorem literal_reflects (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
      (Child fixture) faults size := by
  intro scope id code certified node found _sourceTyped mapping world administrative environment canonical native
    actualContext before store ξ value finalStore _environments heaps _locals _agrees _typed initial admitted completed
  obtain ⟨allowed, other, otherFound, literal, selected⟩ := certified
  have same := Option.some.inj (otherFound.symm.trans found)
  subst other
  have fields := child_fields fixture metadata allowed found
  have nativeWord := literal_word_type literal fields.1
  rw [nativeWord] at literal
  have numeric := selected.evidence (context := SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
    rfl (numeric_runtime_ledger fixture.runtime.rows) evidence
  obtain ⟨sourceValue, coreValue, raw, related, evaluated⟩ := literal.evaluates_with_evidence (registry := registry)
    functions (Program.ofChecked fixture.packet.compiled.sourceProgram)
    (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence numeric
    _ environment before mapping world native store ξ
  obtain ⟨sameValue, sameStore⟩ := evaluation_deterministic evaluated completed.sound
  subst value
  subst finalStore
  have sourceTrace : Dynamic.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
      environment before id sourceValue before := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found) raw
    rw [fields.2]
    exact .nil
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size (.value sourceTrace)
  refine ⟨sourceSize, .value sourceValue, before, mapping, world, sized,
    .value (by simpa only [CompatibleAmbientHeap.payloadModel, nativeWord] using related), heaps,
    .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial, admitted.rows, ?_⟩
  intro value same
  cases same
  rw [fields.1]
  exact ⟨word_typed literal raw, admitted.heap⟩

variable (receipt : PairReceipt fixture root)

def Tuple : GenericExpressionMeaning.Certificate := fun scope id code =>
  scope = parentScope fixture ∧ id = expressionId fixture.packet 6 ∧ code = receipt.tuple

include metadata in
/-- The original physical tuple owns the two actual Source Word rows. -/
theorem PairReceipt.header : CompatibleExpressionTuples.Header
    (.initial fixture.packet.compiled.compatible.checked) (source fixture.packet.named)
    (expressionId fixture.packet 6) fixture.graph.argument
    [expressionId fixture.packet 7, expressionId fixture.packet 8] [wordType, wordType] [receipt.left, receipt.right] := by
  refine ⟨?_, fixture.graph.argumentForm, ?_⟩
  · simpa only [receipt.packed, SourceCoreCompatibleValues.Context.initial] using receipt.metadata
  · exact metadata.argumentType

include metadata in
/-- The finite static tree uses each retained child certificate once. -/
theorem PairReceipt.tree : DataExpressionSequence.Tree (source fixture.packet.named) (Child fixture)
    (parentScope fixture) [expressionId fixture.packet 7, expressionId fixture.packet 8]
    [wordType, wordType] [receipt.left, receipt.right] := by
  have tree := DataExpressionSequence.Tree.cons fixture.parentRows.leftFound receipt.leftCertified
    (DataExpressionSequence.Tree.single fixture.parentRows.rightFound receipt.rightCertified)
  simpa only [metadata.leftType, metadata.rightType] using tree

include metadata in
private theorem children_typed : ExpressionsHaveTypes (source fixture.packet.named)
    (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
    [expressionId fixture.packet 7, expressionId fixture.packet 8] [wordType, wordType] :=
  .cons (SourceCoreChosenOrdinaryAcceptedOuterTyping.left_typed metadata)
    (.cons (SourceCoreChosenOrdinaryAcceptedOuterTyping.right_typed metadata) (.nil _))

include metadata in
/-- Ordered argument meaning uses the original sequence producer once and
then the original tuple core once. Actual reached rows supply the whole post. -/
theorem preserves (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
      (Tuple fixture root receipt) faults size := by
  intro scope id code certified node found _sourceTyped mapping world administrative environment canonical native
    actualContext before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := certified
  have same := Option.some.inj (found.symm.trans fixture.graph.argumentFound)
  subst node
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, heapMetadata, transition⟩ :=
    RecursiveNamedTupleHeadBounds.Stateful.preserves_bounded_with_sequence functions
      (Program.ofChecked fixture.packet.compiled.sourceProgram) evidence callerProtocol size size (Nat.le_refl _)
      fixture.runtime.source_runtime.graph.nodeOccurrencesUnique (PairReceipt.header fixture root metadata receipt)
      initial (CallableIndexedOwnedAdmittedSequenceProducer.preserves bridge initial admitted
        (PairReceipt.tree fixture root metadata receipt)
        fixture.runtime.source_runtime.graph.nodeOccurrencesUnique (children_typed fixture metadata)
        environments heaps locals agrees typed (size + 1)
        (fun child _ => literal_preserves fixture bridge functions metadata evidence child)) trace
  obtain ⟨reached, related⟩ := transition
  refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata,
    reached, related, ?_⟩
  · simpa only [receipt.packed] using evaluated
  · simpa only [receipt.packed, SourceCoreCompatibleValues.Context.initial] using represented
  · simpa only [metadata.argumentType] using
      SourceCoreChosenOrdinaryAcceptedArgumentAdmission.post_admission fixture bridge initial reached admitted trace.sound frame

include metadata in
/-- Reflection reuses the original native tuple decomposition and constructs
its independent Source size and genuine admission at the same returned state. -/
theorem reflects (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
      (Tuple fixture root receipt) faults size := by
  intro scope id code certified node found _sourceTyped mapping world administrative environment canonical native
    actualContext before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  obtain ⟨rfl, rfl, rfl⟩ := certified
  have same := Option.some.inj (found.symm.trans fixture.graph.argumentFound)
  subst node
  have packedCompleted : EvaluationSize size native store
      ((SourceCoreCalls.packArguments [receipt.left, receipt.right]).expression.rename ξ) value finalStore := by
    simpa only [receipt.packed] using completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, heapMetadata, transition⟩ :=
    RecursiveNamedTupleHeadBounds.Stateful.reflects_bounded_with_sequence functions
      (Program.ofChecked fixture.packet.compiled.sourceProgram) evidence callerProtocol size size (Nat.le_refl _)
      (PairReceipt.header fixture root metadata receipt)
      initial (CallableIndexedOwnedAdmittedSequenceProducer.reflects bridge initial admitted
        (PairReceipt.tree fixture root metadata receipt)
        fixture.runtime.source_runtime.graph.nodeOccurrencesUnique (children_typed fixture metadata)
        environments heaps locals agrees typed (size + 1)
        (fun child _ => literal_reflects fixture bridge functions metadata evidence child)) packedCompleted
  obtain ⟨reached, related⟩ := transition
  refine ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps, maps, worlds, frame, heapMetadata,
    reached, related, ?_⟩
  · simpa only [receipt.packed, SourceCoreCompatibleValues.Context.initial] using represented
  · simpa only [metadata.argumentType] using
      SourceCoreChosenOrdinaryAcceptedArgumentAdmission.post_admission fixture bridge initial reached admitted trace.sound frame

include metadata in
/-- Successful pair admission transports the same reached Source heap back to
its real closure context through the authentic outer binder extension. -/
theorem before_typed {index : ProtectedStateTransition.Index}
    (reached : callerProtocol.State index) {value : Dynamic.Value}
    (post : PostAdmission bridge (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
      parameterType (.value value) reached) :
    Dynamic.HeapWellTyped (runtimeContext fixture.packet) index.heap := by
  exact (Dynamic.HeapWellTyped.iff_of_binderExtends metadata.extended).mpr post.at_value.2.heap

include metadata in
/-- The concrete endpoint derives the parent-selected static receipt internally
once. Both admitted meanings use that same tuple and original child family. -/
theorem at_parent
    (parentAccepted : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
      498 (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
      (parentScope fixture) (expressionId fixture.packet 5)
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key) = .ok fixture.calls.parent) :
    ∃ selected : PairReceipt fixture root,
      (∀ size, CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
        (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
        (Tuple fixture root selected) faults size) ∧
      (∀ size, CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
        (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
        (Tuple fixture root selected) faults size) := by
  obtain ⟨selected⟩ := compiler_receipt fixture root parentAccepted
  exact ⟨selected, fun size => preserves fixture root bridge functions metadata evidence selected size,
    fun size => reflects fixture root bridge functions metadata evidence selected size⟩

end Admitted
end Tests.SourceCoreChosenOrdinaryAcceptedPairArgumentBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes
/-! The accepted indirect parent has one physical argument occurrence. Its
original pair outcome proof fixes the actual value and unchanged heap, and
excludes a fault in that same singleton list. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedNamedGeneration
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedOuterTyping

variable (fixture : AcceptedFixture)
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap}

/-- Any actual completed singleton argument trace retains the original pair
value and the same input heap. Source size remains the trace's own grade. -/
theorem values_at {size : Nat} {values : List Dynamic.Value}
    (trace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size (localContext fixture) evidence (source fixture.packet.named) environment before
      [expressionId fixture.packet 6] values after) :
    values = [SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argumentValue] ∧ after = before := by
  have actual := trace.sound
  cases actual with
  | cons head tail =>
    cases tail
    obtain ⟨same, heap⟩ := SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argument_outcome fixture (.value head)
    exact ⟨congrArg (fun value => [value]) (Dynamic.ExpressionOutcome.value.inj same), heap⟩

/-- The original pair's genuine outcome excludes the head fault; the empty
remaining list has no fault constructor. -/
theorem noFault (size : Nat) (reason : Dynamic.SemanticFault)
    (after : Dynamic.Heap)
    (trace : SourceExecutionSize.ExpressionsFault (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size (localContext fixture) evidence (source fixture.packet.named) environment before
      [expressionId fixture.packet 6] reason after) : False := by
  have actual := trace.sound
  cases actual with
  | head fault =>
    have impossible := (SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argument_outcome fixture (.fault fault)).1
    cases impossible
  | tail _ fault => cases fault

/-- Existing ordered pair execution supplies a real sized singleton list;
no completed child law is an input. -/
theorem evaluates : ∃ size,
    SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size (localContext fixture) evidence (source fixture.packet.named) environment before
      [expressionId fixture.packet 6] [SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argumentValue] before := by
  exact SourceExecutionSize.ExpressionsEvaluate.has_size (Dynamic.ExpressionsEvaluate.cons
    (SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argument_evaluates fixture) .nil)

end Tests.SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts
/-! The original accepted parent and chosen lambda retain one initializer
policy. Compiler receipts expose the actual callee, physical arguments and
prepared site without supplying execution, dispatch or body meaning. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedLiteralReturnSiteShells
open CallableIndexedOwnedPreparedMixedBodySiteInputs
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader

/-- The actual fresh let binding precedes this parent occurrence. -/
def parentScope (fixture : AcceptedFixture) : SourceCoreLocalCell.Scope :=
  (fixture.graph.binder.id, fixture.calls.payload) :: initialScope fixture.packet

def parentReason (fixture : AcceptedFixture) : ExpressionId → Word :=
  (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt
    fixture.packet.named.signature.key

abbrev Root (fixture : AcceptedFixture) (caller : ActualHeader fixture)
    (compilation : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode) :=
  LiteralRootReceipt (compiled := fixture.packet.compiled) caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
    498 (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1)
    (parentReason fixture) fixture.calls.initializer

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : Root fixture caller compilation)

abbrev Compiler :=
  CallableIndirectCallCertificates.Receipt root.root.selected.policy root.root.selected.lowerBody
    497 (context fixture.packet.compiled.indexed caller.named) (source fixture.packet.named)
    (parentScope fixture) (expressionId fixture.packet 5) (expressionId fixture.packet 9)
    [expressionId fixture.packet 6] indirectMetadata (parentReason fixture) fixture.calls.parent

/-- Both original and policy-read nodes are authenticated at the same parent. -/
structure ParentReceipt where
  compiler : Compiler fixture root
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
    498 (context fixture.packet.compiled.indexed caller.named) (source fixture.packet.named)
    (parentScope fixture) (expressionId fixture.packet 5) (parentReason fixture) = .ok fixture.calls.parent
  original : compiler.original = fixture.graph.parent
  node : compiler.node = fixture.graph.parent
  parent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler
  prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    fixture.packet.compiled.indexed.ancestry.graph.inputs.callable

/-- This finite extraction consumes the actual selected policy acceptance. -/
theorem at_root (atHeader : HeaderAt fixture caller)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
      498 (context fixture.packet.compiled.indexed caller.named) (source fixture.packet.named)
      (parentScope fixture) (expressionId fixture.packet 5) (parentReason fixture) = .ok fixture.calls.parent) :
    Nonempty (ParentReceipt fixture root) := by
  have ordinary : fixture.packet.compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context fixture.packet.compiled.indexed caller.named).owner ∧
        binding.initializer = expressionId fixture.packet 5)) = none := by
    simpa only [atHeader.named, context, CompatibleNamedBody.bodyContext] using fixture.calls.parentOrdinary
  have pointwise := CallableIndexedOwnedContextualCompilerPolicyProfiles.indirect_policy root.root
    (scope := parentScope fixture) (reasonAt := parentReason fixture)
    fixture.graph.parentFound fixture.graph.parentForm fixture.graph.parentRequirements
    fixture.graph.parentCoercions rfl ordinary
  have read : root.root.selected.policy.readExpression (source fixture.packet.named) (expressionId fixture.packet 5) =
      .ok (fixture.graph.parent, fixture.parentRows.parentCore) := by
    rw [pointwise.read]
    exact fixture.parentRows.parentRead
  obtain ⟨compiler⟩ := CallableIndirectCallCertificates.of_functions
    fixture.graph.parentFound fixture.graph.parentForm pointwise.special read fixture.graph.parentForm accepted
  have original : compiler.original = fixture.graph.parent :=
    Option.some.inj (compiler.found.symm.trans fixture.graph.parentFound)
  have node : compiler.node = fixture.graph.parent := (Prod.mk.inj (Except.ok.inj (compiler.read.symm.trans read))).1
  have nodeId : compiler.node.id = expressionId fixture.packet 5 :=
    (congrArg ExpressionNode.id node).trans (lookupExpression?_sound fixture.graph.parentFound).2
  obtain ⟨prepared⟩ := CallableIndexedOwnedIndirectSourceAdapters.Prepared.of_receipt
    compiler fixture.packet.compiled.indexed.ancestry.graph.inputs.callable [] root.root.callables nodeId
  refine ⟨⟨compiler, accepted, original, node, ?_, prepared⟩⟩
  exact ⟨original.symm ▸ fixture.graph.parentRequirements,
    original.symm ▸ fixture.graph.parentCoercions, rfl⟩

/-- Actual chosen code and parent code belong to one retained root receipt. -/
structure ChosenParentReceipt where
  parent : ParentReceipt fixture root
  chosen : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
    (runtimeContext fixture.packet) [] (initialScope fixture.packet) (expressionId fixture.packet 1) fixture.calls.initializer
  policy : chosen.formation.produced.site.code.policy = root.root.selected.policy
  body : chosen.formation.produced.site.code.lowerBody = root.root.selected.lowerBody
  fuel : chosen.formation.produced.site.code.fuel = 498
  view : chosen.formation.produced.site.code.view = source caller.named
  reason : chosen.formation.produced.site.code.reasonAt = parentReason fixture
  factory : ChosenFactory root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) chosen
  readFuel : chosen.formation.body.readFuel = fixture.packet.compiled.indexed.fuel

private theorem transported_parent
    (originalCompilation : Compilation fixture.packet.compiled.indexed fixture.packet.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode)
    (named : Named) (same : fixture.packet.named = named) :
    let originalRoot := fixture.calls.initializer_root originalCompilation
    let actualRoot := Eq.rec
      (motive := fun (named : Named) (same : fixture.packet.named = named) =>
        LiteralRootReceipt (compiled := fixture.packet.compiled) named
          (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode
          (same ▸ originalCompilation) 498 (source fixture.packet.named) (initialScope fixture.packet)
          (expressionId fixture.packet 1) (parentReason fixture) fixture.calls.initializer)
      originalRoot same
    SourceCoreFunctions.lowerExpressionWithPolicy actualRoot.root.selected.policy actualRoot.root.selected.lowerBody
      498 (context fixture.packet.compiled.indexed named) (source fixture.packet.named)
      (parentScope fixture) (expressionId fixture.packet 5) (parentReason fixture) = .ok fixture.calls.parent := by
  cases same
  exact fixture.calls.parent_at_initializer_root fixture.parentRows fixture.parentAccepted originalCompilation

/-- One original named compilation and initializer selector supply both
receipts. The parent action is never selected as a fresh contextual root. -/
theorem at_original_root (atHeader : HeaderAt fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (metadata : SourceCoreChosenOrdinaryAcceptedBodyMetadata.Receipt fixture.packet fixture.graph)
    (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture) :
    ∃ actualCompilation : Compilation fixture.packet.compiled.indexed caller.named
        (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode,
      ∃ actualRoot : Root fixture caller actualCompilation, Nonempty (ChosenParentReceipt fixture actualRoot) := by
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
        (expressionId fixture.packet 1) (parentReason fixture) fixture.calls.initializer)
    originalRoot atHeader.named.symm
  obtain ⟨parent⟩ := at_root fixture actualRoot atHeader
    (transported_parent fixture originalCompilation caller.named atHeader.named.symm)
  obtain ⟨chosen, policy, body, fuel, view, reason, factory, readFuel⟩ :=
    SourceCoreChosenOrdinaryAcceptedLiteralFactory.chosen_at_root fixture atHeader shape metadata inventory actualRoot
      (by unfold parentReason effectiveDiagnostics; split <;> rfl)
  exact ⟨actualCompilation, actualRoot, ⟨⟨parent, chosen, policy, body, fuel, view, reason, factory, readFuel⟩⟩⟩

end Tests.SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts
/-! The actual accepted named body retains its initialized allocation and
outer return. Finite original compiler inversions authenticate both children,
the marked request and the exact flow; no execution or body law is supplied. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableIndexedNamedGeneration
open CompatibleEncoding (bind_ok)
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader

def request (fixture : AcceptedFixture) : SourceCoreSourceCells.Request :=
  TypedLexicalControl.initializedRequest (source fixture.packet.named) (initialScope fixture.packet)
    fixture.graph.binder fixture.calls.payload

def returned (fixture : AcceptedFixture) : Expr :=
  LocalLoop.returnValue fixture.packet.named.signature.resultType fixture.calls.parent.expression

def emittedFlow (fixture : AcceptedFixture) (allocation : Expr) : Expr :=
  TypedLexicalControl.sequence fixture.packet.named.signature.resultType
    fixture.calls.initializer.expression allocation (returned fixture)

/-- Every field comes from the original named-body compiler action. -/
structure Receipt (fixture : AcceptedFixture) where
  bodyAccepted : SourceCoreLoops.lowerStatementsWithPolicy (policy fixture) 500 (source fixture.packet.named)
    (initialScope fixture.packet) [statementId fixture.packet 0, statementId fixture.packet 4]
    fixture.packet.named.signature.resultType
    (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture)
    fixture.calls.own.fellThroughReason fixture.calls.own.table.escapedReason = .ok fixture.calls.body
  binderAccepted : (policy fixture).lowerBinder (source fixture.packet.named) (initialScope fixture.packet)
    fixture.graph.binder = .ok fixture.calls.payload
  initializerAccepted : (policy fixture).lowerExpression 499 (source fixture.packet.named)
    (initialScope fixture.packet) (expressionId fixture.packet 1)
    (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) = .ok fixture.calls.initializer
  initializerType : fixture.calls.initializer.type = fixture.calls.payload
  parentAccepted : (policy fixture).lowerExpression 498 (source fixture.packet.named)
    (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) (expressionId fixture.packet 5)
    (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) = .ok fixture.calls.parent
  parentType : fixture.calls.parent.type = fixture.packet.named.signature.resultType
  cells : (policy fixture).sourceCells = some (allocator fixture.packet.compiled.indexed fixture.packet.named)
  allocation : SourceCoreAllocationLayouts.Allocation fixture.packet.compiled.indexed.layouts
    fixture.packet.named.signature.key [] (request fixture)
  annotation : SourceCoreCallableIndexedAllocationFrames.Annotated fixture.packet.compiled.indexed.ancestry.layout.frame
    fixture.packet.compiled.indexed.base.globals.length
    (fixture.packet.compiled.indexed.layouts.allocatorAt fixture.packet.named.signature.key []
      (fun error => .sourceAllocation (reprStr error))) (request fixture)
  same : annotation.original = allocation.expression
  allocationAccepted : allocator fixture.packet.compiled.indexed fixture.packet.named (request fixture) = .ok annotation.expression
  flowAccepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (policy fixture) 500 (source fixture.packet.named)
    (initialScope fixture.packet) [statementId fixture.packet 0, statementId fixture.packet 4]
    fixture.packet.named.signature.resultType
    (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) true
    fixture.calls.own.table.escapedReason = .ok (emittedFlow fixture annotation.expression)
  emitted : fixture.calls.body = CompatibleStatements.finish fixture.packet.named.signature.resultType
    (emittedFlow fixture annotation.expression) fixture.calls.own.fellThroughReason fixture.calls.own.table.escapedReason

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

/-- The actual loop policy preserves the fixed read, binder and marked allocator. -/
theorem policy_fields (fixture : AcceptedFixture) :
    (policy fixture).readStatement = SourceCoreCompatibleDataExpressions.readStatement fixture.packet.compiled.compatible.checked ∧
    (policy fixture).sourceCells = some (allocator fixture.packet.compiled.indexed fixture.packet.named) ∧
    (policy fixture).lowerBinder (source fixture.packet.named) (initialScope fixture.packet) fixture.graph.binder =
      binderAction fixture.packet fixture.graph ∧
    (∀ fuel scope id reason, (policy fixture).lowerExpression fuel (source fixture.packet.named) scope id reason =
      SourceCoreGeneralFunctions.lowerContextualExpression fixture.packet.compiled.indexed.base.sourceProgram
        ((representation fixture.packet.compiled.indexed).atContext fixture.packet.named.signature.key [])
        fixture.packet.compiled.indexed.base.sourceProgram.signatures fixture.packet.compiled.indexed.base.locals
        fixture.calls.parents fixture.calls.own.assignments (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
        (context fixture.packet.compiled.indexed fixture.packet.named) fixture.packet.compiled.indexed.base.callableContext
        none none fuel (source fixture.packet.named) scope id reason) := by
  exact ⟨rfl, rfl, rfl, fun _ _ _ _ => rfl⟩

private theorem lowerBinder_missing {catalog : SourceCoreLocalPolymorphism.Catalog}
    {caller : SourceCoreLocalPolymorphism.Key} {active : TypeSystem.Substitution} {source : TypedSource}
    {scope : SourceCoreBasic.Scope} {binder : TypedBinder}
    (missing : catalog.bindings.filter (fun entry => decide (entry.caller = caller ∧ entry.binder.id = binder.id)) = []) :
    ∃ error, SourceCoreLocalPolymorphism.lowerBinder catalog caller active source scope binder = .error error := by
  unfold SourceCoreLocalPolymorphism.lowerBinder SourceCoreLocalPolymorphism.Catalog.binding
  simp only [missing]
  repeat' split
  all_goals exact ⟨_, rfl⟩

/-- The actual local binder is monomorphic: a polymorphic binder needs a
generalized catalog binding, which the actual parent rows exclude. The
initialized `let` therefore takes no snapshot of its scope. -/
theorem binder_monomorphic (fixture : AcceptedFixture) :
    fixture.graph.binder.scheme.quantified.isEmpty = true := by
  cases polymorphic : fixture.graph.binder.scheme.quantified.isEmpty with
  | true => rfl
  | false =>
    have prepared := fixture.calls.binderPrepared
    unfold binderAction SourceCoreGeneralFunctions.contextualBinder at prepared
    rw [polymorphic, if_neg Bool.false_ne_true] at prepared
    have missing : fixture.packet.compiled.indexed.base.locals.bindings.filter (fun entry =>
        decide (entry.caller = fixture.packet.named.signature.key ∧ entry.binder.id = fixture.graph.binder.id)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro entry member
      exact List.any_eq_false.mp fixture.parentRows.generalized entry member
    obtain ⟨error, failed⟩ := lowerBinder_missing (active := []) (source := source fixture.packet.named)
      (scope := initialScope fixture.packet) missing
    rw [failed] at prepared
    cases prepared

/-- One original body acceptance supplies the initialized and returned branches. -/
theorem of_body (fixture : AcceptedFixture) : Nonempty (Receipt fixture) := by
  obtain ⟨readPolicy, cells, binderPolicy, expressionPolicy⟩ := policy_fields fixture
  have bodyAccepted : SourceCoreLoops.lowerStatementsWithPolicy (policy fixture) 500 (source fixture.packet.named)
      (initialScope fixture.packet) [statementId fixture.packet 0, statementId fixture.packet 4]
      fixture.packet.named.signature.resultType
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture)
      fixture.calls.own.fellThroughReason fixture.calls.own.table.escapedReason = .ok fixture.calls.body := by
    simpa only [bodyAction, SourceCoreGeneralFunctions.bodyLowererWithRepresentation,
      fixture.calls.fuel, policy, initialScope, SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason]
      using fixture.calls.bodyCompiled
  have binderAccepted := binderPolicy.trans fixture.calls.binderPrepared
  have initializerAccepted : (policy fixture).lowerExpression 499 (source fixture.packet.named)
      (initialScope fixture.packet) (expressionId fixture.packet 1)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) = .ok fixture.calls.initializer := by
    simpa only [expressionPolicy, contextualAction, SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason]
      using fixture.calls.initializerCompiled
  have parentAccepted : (policy fixture).lowerExpression 498 (source fixture.packet.named)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) (expressionId fixture.packet 5)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) = .ok fixture.calls.parent := by
    simpa only [expressionPolicy, contextualAction, SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason,
      SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope]
      using fixture.calls.parentCompiled
  simp only [SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope] at parentAccepted
  have accepted := bodyAccepted
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, completed⟩ := bind_ok accepted
  have flowGenerated := generated
  rw [SourceCoreLoops.lowerFlowStatementsWithPolicy, readPolicy, fixture.calls.initializedRead] at generated
  simp only [bind, Except.bind, fixture.graph.initializedForm, binderAccepted, initializerAccepted] at generated
  obtain ⟨checked, payloadMatch, generated⟩ := bind_ok generated
  cases checked
  have payloadMatch := ensure_same payloadMatch
  obtain ⟨tail, tailGenerated, generated⟩ := bind_ok generated
  rw [SourceCoreLoops.lowerFlowStatementsWithPolicy, readPolicy, fixture.calls.returnedRead] at tailGenerated
  simp only [bind, Except.bind, fixture.graph.outerReturnForm] at tailGenerated
  rw [parentAccepted] at tailGenerated
  obtain ⟨checked, _, tailGenerated⟩ := bind_ok tailGenerated
  cases checked
  obtain ⟨checked, resultMatch, tailGenerated⟩ := bind_ok tailGenerated
  cases checked
  have resultMatch := ensure_same resultMatch
  have tailEq : tail = returned fixture := Except.ok.inj tailGenerated.symm
  subst tail
  rw [if_pos (binder_monomorphic fixture)] at generated
  simp only [SourceCoreSourceCells.letInitialized, cells] at generated
  obtain ⟨allocationCode, allocationAccepted, generated⟩ := bind_ok generated
  obtain ⟨allocation, annotation, same, allocationEq⟩ :=
    CallableIndexedAllocationCompletion.accepted_receipts
      (fun error => .sourceAllocation (reprStr error)) allocationAccepted
  have flowEq : flow = emittedFlow fixture annotation.expression := by
    cases generated
    rw [allocationEq]
    rfl
  subst flow
  have emitted : fixture.calls.body = CompatibleStatements.finish fixture.packet.named.signature.resultType
      (emittedFlow fixture annotation.expression) fixture.calls.own.fellThroughReason fixture.calls.own.table.escapedReason :=
    (Except.ok.inj completed).symm
  exact ⟨⟨bodyAccepted, binderAccepted, initializerAccepted, payloadMatch.symm, parentAccepted, resultMatch.symm,
    cells, allocation, annotation, same, allocationEq ▸ allocationAccepted, flowGenerated, emitted⟩⟩

/-- Raw Source annotation and native initializer payload remain independent. -/
theorem raw_initializer_type (fixture : AcceptedFixture)
    (metadata : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture) :
    fixture.graph.lambdaNode.type = fixture.graph.binder.scheme.body := by
  rw [metadata.scheme]
  exact fixture.graph.lambdaType

/-- The original Header receives the same emitted body and lexical scope. -/
theorem emitted_at_header (fixture : AcceptedFixture) {caller : ActualHeader fixture}
    (atHeader : HeaderAt fixture caller) (receipt : Receipt fixture) :
    caller.body = CompatibleStatements.finish fixture.packet.named.signature.resultType
      (emittedFlow fixture receipt.annotation.expression)
      fixture.calls.own.fellThroughReason fixture.calls.own.table.escapedReason ∧
    caller.bindings.reverse.map (fun binding => (binding.1.id, binding.2)) = initialScope fixture.packet := by
  exact ⟨atHeader.body.trans receipt.emitted, congrArg (fun bindings =>
    bindings.reverse.map (fun binding => (binding.1.id, binding.2))) atHeader.bindings⟩

/-- Body and both expression children retain the actual supplied chosen root. -/
structure ChosenOuterReceipt (fixture : AcceptedFixture) {caller : ActualHeader fixture}
    {compilation : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation) where
  outer : Receipt fixture
  chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt fixture root

/-- The existing original initializer selector runs once. Body extraction uses
the independently retained actual named acceptance without another selector. -/
theorem at_original_root (fixture : AcceptedFixture) {caller : ActualHeader fixture}
    (atHeader : HeaderAt fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (metadata : SourceCoreChosenOrdinaryAcceptedBodyMetadata.Receipt fixture.packet fixture.graph)
    (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture) :
    ∃ actualCompilation : Compilation fixture.packet.compiled.indexed caller.named
        (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode,
      ∃ actualRoot : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller actualCompilation,
        Nonempty (ChosenOuterReceipt fixture actualRoot) := by
  obtain ⟨actualCompilation, actualRoot, ⟨chosen⟩⟩ :=
    SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.at_original_root fixture atHeader shape metadata inventory
  obtain ⟨outer⟩ := of_body fixture
  exact ⟨actualCompilation, actualRoot, ⟨⟨outer, chosen⟩⟩⟩

end Tests.SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedInitializedEntry
/-! One real formation and one marked allocation connect the accepted lambda
initializer to its actual admitted parent entry. The actual creation scope is
empty, so the formation copies no cell and forms over the original capture.
The original formation history is retained through allocation; the parent index
uses the same extended capture. Initial heap, frame, capture, all-row admission
and allocator readiness remain genuine inputs. No body execution law is an input. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedInitializedEntry
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  (atHeader : HeaderAt fixture caller)
  (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
  (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
  (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata fixture.packet)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt fixture root)
  (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt fixture)

include atHeader typing in
/-- The Source binder type comes from the same original lambda occurrence. -/
theorem binder_type : fixture.graph.binder.scheme.body =
    FunctionValues.sourceType (chosen.chosen.formation.function []) := by
  have found := chosen.chosen.formation.produced.site.code.sourceFound
  rw [chosen.chosen.formation.produced.identifier] at found
  change (source caller.named).lookupExpression? (expressionId fixture.packet 1) = some _ at found
  have foundFixture : (source fixture.packet.named).lookupExpression? (expressionId fixture.packet 1) = some chosen.chosen.formation.produced.site.code.sourceNode := by
    simpa only [atHeader.named] using found
  have sameNode := Option.some.inj (foundFixture.symm.trans fixture.graph.lambdaFound)
  have raw := chosen.chosen.formation.sourceType
  rw [sameNode] at raw
  exact (SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.raw_initializer_type fixture typing).symm.trans raw

include outer in
/-- The accepted initializer payload is the original checked callable type. -/
theorem payload_type : fixture.calls.payload = CallableContract.functionType
    (chosen.chosen.formation.code []).receipt.parameterCore
    (chosen.chosen.formation.code []).receipt.resultCore := by
  have emitted := chosen.chosen.formation.produced.emitted
  have native := RecursiveNamedLambdaFormationHeads.site_native_type (values := .initial fixture.packet.compiled.compatible.checked) (caller := caller) chosen.chosen.formation.produced.site
  exact outer.initializerType.symm.trans ((congrArg SourceCoreBasic.LoweredExpr.type emitted).symm.trans native)

variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  (captured : Captures fixture.packet.compiled.indexed mapping world (initialScope fixture.packet)
    (chosen.chosen.formation.function []).captured actual)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial fixture.packet.compiled.compatible.checked) caller)

/-- A lambda over an empty creation scope emits no copies: its emitted
expression is the decorated lambda itself. -/
theorem emitted_without_copies {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) (empty : scope = [])
    (copied : code.policy.snapshotLambda code.id = true) :
    code.lowered.expression = code.expression := by
  have accepted := code.emitted_copied copied
  subst empty
  have identity : SourceCoreSourceCells.scopeCopyRenaming code.view [] (fun index => index) = Renaming.id := by
    funext index
    simp [SourceCoreSourceCells.scopeCopyRenaming, SourceCoreSourceCells.copiedSlots,
      SourceCoreSourceCells.copyRenaming, Renaming.id]
  simp only [SourceCoreSourceCells.copyScope, SourceCoreSourceCells.copyChain, identity, Expr.rename_id] at accepted
  exact (Except.ok.inj accepted).symm

include checked in
/-- The actual named body has no inputs, so the lambda's creation scope is empty. -/
theorem initial_scope_empty : initialScope fixture.packet = [] := by
  simp only [initialScope, checked.named_inputs, List.reverse_nil, List.map_nil]

/-- Recapture retains the actual accepted initializer expression and renaming. -/
theorem initializer_expression :
    ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext).code.lowered.expression.rename
      (CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext).captured.embedding) =
      fixture.calls.initializer.expression.rename captured.embedding := by
  exact congrArg (fun lowered : SourceCoreBasic.LoweredExpr => lowered.expression.rename captured.embedding)
    chosen.chosen.formation.produced.emitted

/-- The extended index is exactly the parent index with the same capture.
Only map/world proofs change; formation history is not reconstructed. -/
theorem index_after_allocation {nextMap : LocationMap} {nextWorld : StoreTyping}
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld) :
    CallableIndexedOwnedChosenOrdinaryStoredMembers.extendIndex
      (CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext) maps worlds =
    CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] (captured.extend maps worlds) prefixContext := by
  rfl

local notation "i0" => CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext
local notation "functions" => CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
  (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts
local notation "model" => CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions
local notation "frame" => fixture.packet.compiled.indexed.ancestry.layout.frame

variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {administrative : Core.Context} {canonical : Environment} {before after : Dynamic.Heap} {store : Store}
  {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
  (initial : State headers keys ⟨initialScope fixture.packet, mapping, world, before, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ initial)

local notation "history0" => CallableIndexedOwnedPreparedOrdinaryLambdaFormation.history_at
  (i0).captured (i0).code (i0).support owner initial packet
local notation "closureValue" => value (i0).code (i0).captured.embedding (history0).native actual
local notation "producer" => CallableIndexedOwnedNestedCanonicalState.markedProducer (headers := headers) owner caller model
local notation "first" => (⟨initial, packet⟩ : (CallableIndexedOwnedNestedCanonicalState.protocol owner caller).State _)

/-- Every component is from one real initialized allocation at the original
formation history. The parent receives the exact reached state and all rows. -/
def InitializedAt : Prop :=
  ∃ allocationCapture,
    CallableIndexedAllocationCompletion.Captures (closureValue :: canonical)
      (SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.request fixture).references
      (initialScope fixture.packet) allocationCapture ∧
    RuntimeValueHasType world allocationCapture (SourceCoreSourceCells.captureType (initialScope fixture.packet))
      fixture.packet.compiled.indexed.layouts.definitions ∧
    let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
      SourceCoreHeapMarkers.markerValue outer.allocation.entry.layout allocationCapture, .inRight .unit closureValue]
    let nextWorld := world ++ [(frame).type, outer.allocation.entry.layout.type, OptionalCell.cellType fixture.calls.payload]
    let nextMap := mapping ++ [store.length + 2]
    let nextRef := Value.cellRef (OptionalCell.cellType fixture.calls.payload) (store.length + 2)
    Evaluates (closureValue :: actual) store (outer.annotation.expression.rename captured.embedding.lift) nextRef nextStore ∧
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog fixture.packet.compiled.compatible.checked.catalog)
      nextMap nextWorld administrative (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture)
      [(fixture.graph.binder.id, location)] (nextRef :: canonical) fixture.packet.compiled.indexed.layouts.definitions ∧
    CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry functions nextMap nextWorld after nextStore ∧
    Dynamic.EnvironmentAgrees after (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture).locals
      [(fixture.graph.binder.id, location)] ∧
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) captured.embedding).lift
      (nextRef :: canonical) (nextRef :: closureValue :: actual) ∧
    RuntimeEnvironmentHasTypes nextWorld (nextRef :: closureValue :: actual)
      (OptionalCell.referenceType fixture.calls.payload :: fixture.calls.payload :: captured.actualContext)
      fixture.packet.compiled.indexed.layouts.definitions ∧
    (nextRef :: canonical)[(SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture).length + 1 +
      fixture.packet.compiled.indexed.base.globals.length]? = some (.cellRef (frame).type contextLocation) ∧
    nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
    AdministrativePreserved mapping store nextMap nextStore ∧
    ∃ (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld),
      Dynamic.HeapMetadataExtend before after ∧
      ReferenceRepresents nextMap nextWorld location (store.length + 2) fixture.calls.payload ∧
      CallableIndexedOwnedChosenOrdinaryStoredMembers.ChosenStoredAt root.root
        (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults
        (CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] (captured.extend maps worlds) prefixContext)
        history0 after nextStore location ∧
      ∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol owner caller).State
          ⟨SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        (CallableIndexedOwnedNestedCanonicalState.protocol owner caller).Relates first reached ∧
        Relates initial reached.val ∧
        Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
          (CallableIndexedOwnedNestedCallerProtocol.carrier owner caller))
          (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) reached

include atHeader shape typing checked in
/-- The genuine Source initializer is formed once over the empty creation
scope, which copies nothing, then its actual marked allocator runs once. Input
captures, heap and every caller row stay explicit. -/
theorem initialized_entry
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := fixture.packet.compiled.indexed)
      (values := .initial fixture.packet.compiled.compatible.checked)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram) headers owner.key.locations 1
      (initialScope fixture.packet) captured.canonical owner.key.frameLocation)
    (stored : RuntimeStoreHasTypes world store fixture.packet.compiled.indexed.layouts.definitions)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog fixture.packet.compiled.compatible.checked.catalog)
      mapping world administrative (initialScope fixture.packet) [] canonical fixture.packet.compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry functions
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before (runtimeContext fixture.packet).locals [])
    (agrees : EnvironmentsAgree captured.embedding canonical actual)
    (reference : canonical[(initialScope fixture.packet).length + 1 + fixture.packet.compiled.indexed.base.globals.length]? =
      some (.cellRef (frame).type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before fixture.graph.binder.scheme.body
      (some (.closure (i0).function)) location after)
    (ready : (producer).Ready first contextLocation native)
    (admitted : Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
      (CallableIndexedOwnedNestedCallerProtocol.carrier owner caller)) (runtimeContext fixture.packet) first) :
    Dynamic.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (runtimeContext fixture.packet) [] (source caller.named) [] before
      (expressionId fixture.packet 1) (.closure (i0).function) before ∧
    Evaluates actual store (fixture.calls.initializer.expression.rename captured.embedding)
      (.inRight .word closureValue) store ∧
    (∀ result finalStore, Evaluates actual store (fixture.calls.initializer.expression.rename captured.embedding) result finalStore →
      result = .inRight .word closureValue ∧ finalStore = store) ∧
    InitializedAt fixture inventory root chosen outer captured prefixContext owner initial packet
      (registry := registry) (faults := faults) (administrative := administrative) (after := after)
      (contextLocation := contextLocation) (native := native) (location := location) := by
  have lowered := emitted_without_copies (i0).code (initial_scope_empty fixture checked)
    (chosen.chosen.formation.snapshots [])
  have frameReference : (i0).captured.canonical[(i0).code.referenceIndex]? =
      some (.cellRef (frame).type owner.key.frameLocation) := by
    rw [CallableIndexedOwnedPreparedOrdinaryLambdaFormation.reference_index (i0).captured (i0).code (i0).support]
    exact observed.reference
  have frameRead : store.read? owner.key.frameLocation =
      some (SourceCoreCallableIndexedFrames.encode frame (history0).native) := by
    have actualRead := (initial.rows owner.position).authority.frame.read
    rw [(initial.rows owner.position).frame_eq] at actualRead
    exact actualRead
  have evaluated : Evaluates actual store ((i0).code.lowered.expression.rename (i0).captured.embedding)
      (.inRight .word closureValue) store := by
    rw [lowered]
    exact CallableIndexedLambdaValues.expression_evaluates (i0).captured (i0).code history0 frameReference frameRead
  have determined : ∀ result finalStore,
      Evaluates actual store ((i0).code.lowered.expression.rename (i0).captured.embedding) result finalStore →
        result = .inRight .word closureValue ∧ finalStore = store :=
    fun _ _ completed => evaluation_deterministic completed evaluated
  obtain ⟨future, _, finalStored, resultTyped⟩ := evaluation_preserves_type evaluated
    ((i0).code.typed.rename (i0).captured.respects) (i0).captured.typed stored
  have sameWorld : future = world := finalStored.world_eq.trans stored.world_eq.symm
  subst future
  have nativeTyped : RuntimeValueHasType world closureValue
      (CallableContract.functionType (i0).code.receipt.parameterCore (i0).code.receipt.resultCore)
      fixture.packet.compiled.indexed.layouts.definitions := by
    cases resultTyped with
    | inRight typed => exact typed
  have member : CallableIndexedOwnedChosenOrdinaryStoredMembers.ChosenAt root.root
      (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults i0 history0 :=
    .ordinary owner (.formed chosen.chosen chosen.factory [] captured prefixContext)
      (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.source_origin (i0).captured (i0).code (i0).support
        owner initial packet) rfl observed
      (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.reference_index (i0).captured (i0).code (i0).support)
      nativeTyped
  have sourceTrace := CallableIndexedLambdaValues.source_formation (i0).code
    (Program.ofChecked fixture.packet.compiled.sourceProgram) (.nil before)
    chosen.chosen.formation.ordinary chosen.chosen.formation.coercions
  have valueTyped := SourceCoreChosenOrdinaryAcceptedInitializerAdmission.receipt_value_has_type
    fixture shape [] atHeader chosen.chosen locals
  rw [SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.raw_initializer_type fixture typing] at valueTyped
  have mono : fixture.graph.binder.scheme.quantified = [] := by rw [typing.scheme]; rfl
  have ordinary : (source fixture.packet.named).inputs.any (fun input => decide (input.id = fixture.graph.binder.id)) = false := by
    rw [checked.inputs]; rfl
  have allocationPost := CallableIndexedOwnedChosenOrdinaryInitializedAllocationState.allocate_initialized
    root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) inventory.contracts
    (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (CallableIndexedOwnedNestedCallerProtocol.carrier owner caller))
    rfl (CallableIndexedAmbient.frame_registered fixture.packet.compiled.indexed) producer mono typing.extended ordinary
    outer.allocation outer.annotation outer.same (binder_type fixture atHeader typing root chosen)
    (payload_type fixture root chosen outer) member valueTyped environments heaps locals agrees captured.typed
    reference read allocated first ready admitted
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [CallableIndexedOwnedChosenOrdinaryFormedMembers.index,
      CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation.function,
      CallableIndexedLambdaGeneration.closure, CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation.code,
      RecursiveNamedLambdaFormationHeads.recaptureCode, chosen.chosen.formation.produced.identifier]
      using sourceTrace
  · simpa only [initializer_expression fixture root chosen captured prefixContext] using evaluated
  · simpa only [initializer_expression fixture root chosen captured prefixContext] using determined
  · exact allocationPost

end Tests.SourceCoreChosenOrdinaryAcceptedInitializedEntry
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedParentEntryReceipts
/-! The retained parent and chosen closure share one original root. Its actual
argument acceptance supplies the pair, and its actual reference acceptance
supplies the initialized callee post at the current caller state. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedParentEntryReceipts
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedLiteralReturnSiteShells CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission


private def named_compilation (fixture : AcceptedFixture) {named target : Named}
    (same : named = target)
    (compilation : Compilation fixture.packet.compiled.indexed named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode) :
    Compilation fixture.packet.compiled.indexed target
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode := by
  cases same
  exact compilation

private def named_root (fixture : AcceptedFixture) {named target : Named}
    (same : named = target)
    {compilation : Compilation fixture.packet.compiled.indexed named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    (root : LiteralRootReceipt (compiled := fixture.packet.compiled) named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
      498 (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) fixture.calls.initializer) :
    LiteralRootReceipt (compiled := fixture.packet.compiled) target
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode
      (named_compilation fixture same compilation)
      498 (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) fixture.calls.initializer := by
  cases same
  exact root

private theorem named_policy (fixture : AcceptedFixture) {named target : Named}
    (same : named = target)
    {compilation : Compilation fixture.packet.compiled.indexed named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    (root : LiteralRootReceipt (compiled := fixture.packet.compiled) named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
      498 (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) fixture.calls.initializer) :
    (named_root fixture same root).root.selected.policy = root.root.selected.policy ∧
      (named_root fixture same root).root.selected.lowerBody = root.root.selected.lowerBody := by
  cases same
  exact ⟨rfl, rfl⟩

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  (atHeader : HeaderAt fixture caller)
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt fixture root)

/-- Only the authentic Header named index is transported. -/
def fixture_compilation : Compilation fixture.packet.compiled.indexed fixture.packet.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode :=
  named_compilation fixture atHeader.named compilation

/-- This is the supplied root after the same dependent named-index transport. -/
def fixture_root : LiteralRootReceipt (compiled := fixture.packet.compiled) fixture.packet.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode
    (fixture_compilation fixture atHeader (compilation := compilation))
    498 (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1)
    (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) fixture.calls.initializer := named_root fixture atHeader.named root

private theorem action_eq (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) :
    SourceCoreFunctions.lowerExpressionWithPolicy
      (fixture_root fixture atHeader root).root.selected.policy
      (fixture_root fixture atHeader root).root.selected.lowerBody fuel
      (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named) scope id
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) =
    SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody fuel
      (context fixture.packet.compiled.indexed caller.named) (source fixture.packet.named) scope id
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) := by
  obtain ⟨policy, body⟩ := named_policy fixture atHeader.named root
  rw [show (fixture_root fixture atHeader root).root.selected.policy = root.root.selected.policy from policy,
    show (fixture_root fixture atHeader root).root.selected.lowerBody = root.root.selected.lowerBody from body,
    congrArg (context fixture.packet.compiled.indexed) atHeader.named]

section Pair
universe u
variable {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (metadata : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture) (evidence : Dynamic.EvidenceEnvironment)

include metadata in
/-- Actual parent497 singleton acceptance identifies the same selected tuple.
Its admitted meanings retain the arbitrary actual receiving model. -/
theorem pair_at_chosen_parent :
    ∃ pair : SourceCoreChosenOrdinaryAcceptedPairArgumentBounds.PairReceipt fixture (fixture_root fixture atHeader root),
      chosen.parent.compiler.codes = [pair.tuple] ∧
      DataExpressionSequence.Tree (source fixture.packet.named)
        (SourceCoreChosenOrdinaryAcceptedPairArgumentBounds.Tuple fixture (fixture_root fixture atHeader root) pair) (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture)
        [expressionId fixture.packet 6] [parameterType] [pair.tuple] ∧
      (∀ size, CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
        (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
        (SourceCoreChosenOrdinaryAcceptedPairArgumentBounds.Tuple fixture (fixture_root fixture atHeader root) pair) faults size) ∧
      (∀ size, CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
        (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
        (SourceCoreChosenOrdinaryAcceptedPairArgumentBounds.Tuple fixture (fixture_root fixture atHeader root) pair) faults size) := by
  have accepted : SourceCoreFunctions.lowerExpressionWithPolicy
      (fixture_root fixture atHeader root).root.selected.policy
      (fixture_root fixture atHeader root).root.selected.lowerBody 498
      (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
      (SourceCoreChosenOrdinaryAcceptedPairArgumentBounds.parentScope fixture) (expressionId fixture.packet 5) (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) = .ok fixture.calls.parent := by
    exact (action_eq fixture atHeader root 498 (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) (expressionId fixture.packet 5)).trans chosen.parent.accepted
  obtain ⟨pair, preserves, reflects⟩ := SourceCoreChosenOrdinaryAcceptedPairArgumentBounds.at_parent fixture (fixture_root fixture atHeader root)
    bridge functions metadata evidence (registry := registry) (faults := faults) accepted
  have tupleAccepted := pair.tupleAccepted
  change SourceCoreFunctions.lowerExpressionWithPolicy
    (fixture_root fixture atHeader root).root.selected.policy
    (fixture_root fixture atHeader root).root.selected.lowerBody 497
    (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
    (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) (expressionId fixture.packet 6)
    (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) = .ok pair.tuple at tupleAccepted
  rw [action_eq fixture atHeader root 497 (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) (expressionId fixture.packet 6)] at tupleAccepted
  have arguments := chosen.parent.compiler.argumentsAccepted
  simp only [List.mapM_cons, List.mapM_nil, tupleAccepted, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at arguments
  have tree := DataExpressionSequence.Tree.single fixture.graph.argumentFound
    (show SourceCoreChosenOrdinaryAcceptedPairArgumentBounds.Tuple fixture (fixture_root fixture atHeader root) pair (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture)
      (expressionId fixture.packet 6) pair.tuple from ⟨rfl, rfl, rfl⟩)
  exact ⟨pair, arguments.symm, by simpa only [metadata.argumentType] using tree, preserves, reflects⟩

end Pair

private theorem empty_owned : SourceCompilationPlan.ordinaryOwnedRequirements? fixture.graph.callee = some [] := by
  unfold SourceCompilationPlan.ordinaryOwnedRequirements?
  rw [fixture.parentRows.calleeRequirements, fixture.parentRows.calleeCoercions]
  rfl

include atHeader in
/-- Finite reference inversion retains the original root's fixed read fuel. -/
private theorem callee_read_receipts :
    SourceCoreCompatibleDataExpressions.readExpression fixture.packet.compiled.compatible.checked
      (source fixture.packet.named) (expressionId fixture.packet 9) =
        .ok (fixture.graph.callee, chosen.parent.compiler.calleeCode.type) ∧
    SourceCoreCompatibleDataExpressions.lowerRead fixture.packet.compiled.indexed.fuel
      (.initial fixture.packet.compiled.compatible.checked) (source fixture.packet.named)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) (expressionId fixture.packet 9)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture (expressionId fixture.packet 9)) = .ok chosen.parent.compiler.calleeCode.expression := by
  let normalized := fixture_root fixture atHeader root
  have pointwise := SourceCoreChosenOrdinaryAcceptedStaticInventory.ordinary_policy normalized.root
    (childScope := SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) fixture.graph.calleeFound
    (.inl ⟨_, _, fixture.graph.calleeForm, fixture.parentRows.generalized⟩)
    (empty_owned fixture) fixture.parentRows.calleeCoercions (.inl fixture.parentRows.calleeRequirements)
    fixture.parentRows.calleeOrdinary
  have accepted : SourceCoreFunctions.lowerExpressionWithPolicy normalized.root.selected.policy normalized.root.selected.lowerBody 497
      (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) (expressionId fixture.packet 9)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) = .ok chosen.parent.compiler.calleeCode :=
    (action_eq fixture atHeader root 497 (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) (expressionId fixture.packet 9)).trans chosen.parent.compiler.calleeAccepted
  have owner : (expressionId fixture.packet 9).occurrence.owner = (source fixture.packet.named).owner := rfl
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, fixture.graph.calleeFound, fixture.graph.calleeForm, bind, Except.bind,
    pure, Except.pure] at accepted
  have bypass := pointwise.special (fun budget childSource childScope childId childReasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy normalized.root.selected.policy normalized.root.selected.lowerBody
      (min budget 496) (context fixture.packet.compiled.indexed fixture.packet.named)
      childSource childScope childId childReasonAt) 497
  cases hook : normalized.root.selected.policy.lowerSpecial? <;> simp only [hook] at accepted bypass
  all_goals simp only [SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason] at accepted bypass
  all_goals
    try rw [bypass] at accepted
    rw [pointwise.read] at accepted
    cases read : SourceCoreCompatibleDataExpressions.readExpression fixture.packet.compiled.compatible.checked
        (source fixture.packet.named) (expressionId fixture.packet 9) with
    | error error => simp [read] at accepted
    | ok pair =>
      obtain ⟨node, type⟩ := pair
      have same := Option.some.inj ((CompatibleExpressionReads.metadata_of_read read).found.symm.trans fixture.graph.calleeFound)
      subst node
      simp only [read, fixture.graph.calleeForm] at accepted
      rw [normalized.lowerRead] at accepted
      cases generated : SourceCoreCompatibleDataExpressions.lowerRead fixture.packet.compiled.indexed.fuel
          (.initial fixture.packet.compiled.compatible.checked) (source fixture.packet.named)
          (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) (expressionId fixture.packet 9)
          (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture (expressionId fixture.packet 9)) with
      | error error =>
        simp only [SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason] at generated
        simp [generated] at accepted
      | ok expression =>
        simp only [SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason] at generated
        simp only [generated, Except.ok.injEq] at accepted
        have typeEq := congrArg SourceCoreBasic.LoweredExpr.type accepted
        have exprEq := congrArg SourceCoreBasic.LoweredExpr.expression accepted
        exact ⟨congrArg (fun t => Except.ok (fixture.graph.callee, t)) typeEq, congrArg Except.ok exprEq⟩

private theorem binder_declared : fixture.graph.binder ∈ SourceCoreDataPlaces.declaredBinders (source fixture.packet.named) := by
  apply List.mem_append.mpr
  apply Or.inr
  apply List.mem_flatMap.mpr
  refine ⟨.statement fixture.graph.initialized, (lookupStatement?_sound fixture.graph.initializedFound).1, ?_⟩
  simp only [fixture.graph.initializedForm]
  exact List.mem_singleton_self _

include atHeader in
/-- The original Header parameter scope and genuine outer let extension supply
the actual reference declaration, independently of native projection. -/
theorem parent_declarations (metadata : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture) :
    CompatibleExpressionReads.ScopeDeclarations (source fixture.packet.named) (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture)
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) := by
  have initial := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)
    (values := .initial fixture.packet.compiled.compatible.checked)
    (prepared := fixture.packet.compiled.indexed.ancestry)
    (program := Program.ofChecked fixture.packet.compiled.sourceProgram) caller
  have declarations : CompatibleExpressionReads.ScopeDeclarations (source fixture.packet.named)
      (initialScope fixture.packet) (runtimeContext fixture.packet) := by
    simpa only [atHeader.source, atHeader.context, atHeader.bindings,
      RecursiveNamedCatalogNativeContexts.bodyScope, initialScope] using initial
  exact RecursiveNamedHeaderScopeDeclarations.scope_bind fixture.calls.payload
    (binder_declared fixture) declarations metadata.extended

section Callee
universe u
variable {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (metadata : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture) (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
  (evidence : Dynamic.EvidenceEnvironment)
  {i : CallableIndexedOwnedPreparedRuntimeFamilyMembers.OrdinaryIndex fixture.packet.compiled}
  {history : History i.code} {administrative : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {location : Dynamic.Location}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial fixture.packet.compiled.compatible.checked).registry registry)
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog fixture.packet.compiled.compatible.checked.catalog)
    i.mapping i.world administrative (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) environment canonical fixture.packet.compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry
    (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
      (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts)
    i.mapping i.world heap store)
  (locals : Dynamic.EnvironmentAgrees heap (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture).locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (stored : CallableIndexedOwnedChosenOrdinaryStoredMembers.ChosenStoredAt root.root
    (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults i history heap store location)
  (lookup : Dynamic.Environment.LooksUp environment fixture.graph.binder.id location)
  (initial : callerProtocol.State ⟨SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture, i.mapping, i.world, heap, store, canonical⟩)
  (admitted : Admission bridge (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) initial)

include atHeader metadata extension environments heaps locals agrees stored lookup admitted in
/-- One original initialized-read producer returns the genuine callee trace,
full post and positive selection at the same input state and stored member. -/
theorem callee_at_parent :
    ∃ sourceSize,
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram) sourceSize
        (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named) environment heap
        (expressionId fixture.packet 9) (.closure i.function) heap ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry) (actual := actual) (ξ := ξ)
        (calleeNode := chosen.parent.compiler.calleeNode) (context := SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
        bridge (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
          (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts)
        chosen.parent.compiler initial (.closure i.function) heap
        (value i.code i.captured.embedding history.native i.capturedActual) store i.mapping i.world ∧
      CallableIndexedOwnedChosenOrdinaryLambdaValues.Selected
        (headers := headers) (keys := keys) (registry := registry) (faults := faults)
        (mapping := i.mapping) (world := i.world) (raw := chosen.parent.compiler.calleeNode.type)
        (function := i.function) (native := value i.code i.captured.embedding history.native i.capturedActual)
        (type := chosen.parent.compiler.calleeCode.type) root.root
        (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) ∧
      CallableIndexedOwnedChosenOrdinaryStoredMembers.ChosenStoredAt root.root
        (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults i history heap store location := by
  obtain ⟨read, generated⟩ := callee_read_receipts fixture atHeader root chosen
  have sourceTyped : ExpressionHasType (source fixture.packet.named) (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
      (expressionId fixture.packet 9) fixture.graph.callee.type := by
    simpa only [metadata.calleeType] using SourceCoreChosenOrdinaryAcceptedOuterTyping.callee_typed metadata
  obtain ⟨certificate, typeEq, binding⟩ := CompatibleExpressionReads.loweredRead_of_accepted generated read
    fixture.runtime.source_runtime.graph.nodeOccurrencesUnique (parent_declarations fixture atHeader metadata) sourceTyped
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans fixture.graph.calleeFound)
  have formEq := certificate.form.symm.trans (nodeEq ▸ fixture.graph.calleeForm)
  have binderEq := (ExpressionForm.reference.inj formEq).2
  have pointwise := SourceCoreChosenOrdinaryAcceptedStaticInventory.ordinary_policy
    (fixture_root fixture atHeader root).root (childScope := SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) fixture.graph.calleeFound
    (.inl ⟨_, _, fixture.graph.calleeForm, fixture.parentRows.generalized⟩) (empty_owned fixture)
    fixture.parentRows.calleeCoercions (.inl fixture.parentRows.calleeRequirements) fixture.parentRows.calleeOrdinary
  have policyEq := (named_policy fixture atHeader.named root).1
  have actualRead := chosen.parent.compiler.calleeRead
  have readPolicy : root.root.selected.policy.readExpression (source fixture.packet.named) (expressionId fixture.packet 9) =
      SourceCoreCompatibleDataExpressions.readExpression fixture.packet.compiled.compatible.checked (source fixture.packet.named) (expressionId fixture.packet 9) := by
    rw [← policyEq]
    exact pointwise.read
  have sameRead := actualRead.symm.trans (readPolicy.trans read)
  have sameNode : chosen.parent.compiler.calleeNode = certificate.node :=
    (Prod.mk.inj (Except.ok.inj sameRead)).1.trans nodeEq.symm
  have actualLookup : Dynamic.Environment.LooksUp environment certificate.binder location := by
    have sameBinder := ReferenceResolution.local.inj binderEq
    exact sameBinder.symm ▸ lookup
  exact CallableIndexedOwnedChosenOrdinaryInitializedReadAdmission.callee_post
    root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) certificate inventory.contracts
    extension binding fixture.runtime.source_runtime.graph.nodeOccurrencesUnique environments heaps locals agrees stored actualLookup
    bridge chosen.parent.compiler initial rfl sameNode typeEq.symm (nodeEq.symm ▸ sourceTyped) admitted

end Callee
end Tests.SourceCoreChosenOrdinaryAcceptedParentEntryReceipts
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedParentPreservationBounds
/-! The actual initialized fixture callee and original Source parent children
supply one admitted argument sequence and literal application. The returned
caller keeps all maps, worlds, rows, heap typing and the original whole pool. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedParentPreservationBounds
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader

universe u
variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  (atHeader : HeaderAt fixture caller)
  (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
  (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt fixture root)
  {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {mapping : LocationMap} {world : StoreTyping} {actualCapture : Environment}
  (captured : Captures fixture.packet.compiled.indexed mapping world (initialScope fixture.packet)
    (chosen.chosen.formation.function []).captured actualCapture)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial fixture.packet.compiled.compatible.checked) caller)
  (history : History (chosen.chosen.formation.code []))
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming} {location : Dynamic.Location}

local notation "index" => CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext
local notation "functions" => CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
  (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts
local notation "model" => CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions
local notation "localContext" => SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture
local notation "parentScope" => SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture

variable (evidence : Dynamic.EvidenceEnvironment)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial fixture.packet.compiled.compatible.checked).registry registry)
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog fixture.packet.compiled.compatible.checked.catalog)
    mapping world administrative (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) environment canonical fixture.packet.compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry
    (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture).locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext fixture.packet.compiled.indexed.layouts.definitions)
  (stored : CallableIndexedOwnedChosenOrdinaryStoredMembers.ChosenStoredAt root.root
    (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults
    (CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext) history before store location)
  (lookup : Dynamic.Environment.LooksUp environment fixture.graph.binder.id location)
  (initial : callerProtocol.State ⟨SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) initial)

include stored lookup in
/-- Only the readable ordinary Source cell determines this callee outcome.
The known trace comes from the original initialized read producer. -/
private theorem callee_outcome {knownSize : Nat}
    (known : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      knownSize localContext evidence (source fixture.packet.named) environment before
      (expressionId fixture.packet 9) (.closure (index).function) before)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      localContext evidence (source fixture.packet.named) environment before (expressionId fixture.packet 9) outcome after) :
    outcome = .value (.closure (index).function) ∧ after = before := by
  obtain ⟨_member, target, _reference, read, _nativeRead⟩ := stored
  exact CompatibleExpressionReads.source_outcome_unique fixture.runtime.source_runtime.graph.nodeOccurrencesUnique
    (lookupExpression?_sound fixture.graph.calleeFound) fixture.graph.calleeForm fixture.parentRows.calleeCoercions
    lookup read rfl trace (.value known.sound)

include stored lookup in
/-- Finite inversion retains the original measured Source callee, ordered
argument child and closure call; the actual initialized read excludes earlier
faults without a whole-language preservation assumption. -/
private theorem called_at_parent {knownSize : Nat}
    (known : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      knownSize localContext evidence (source fixture.packet.named) environment before
      (expressionId fixture.packet 9) (.closure (index).function) before)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size localContext evidence (source fixture.packet.named) environment before
      (expressionId fixture.packet 5) outcome after) :
    ∃ calleeSize argumentsSize callSize arguments,
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
        calleeSize localContext evidence (source fixture.packet.named) environment before
        (expressionId fixture.packet 9) (.closure (index).function) before ∧
      SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked fixture.packet.compiled.sourceProgram)
        argumentsSize localContext evidence (source fixture.packet.named) environment before
        [expressionId fixture.packet 6] arguments before ∧
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
        callSize localContext evidence (index).function.evidence before (.closure (index).function) arguments outcome after ∧
      calleeSize < size ∧ argumentsSize < size ∧ callSize < size := by
  have original := CallableIndirectCallSourceBounds.indirect_inv_sized fixture.graph.parentFound
    fixture.graph.parentForm fixture.graph.parentCoercions
    fixture.runtime.source_runtime.graph.nodeOccurrencesUnique trace
  cases original with
  | calleeFault child _ =>
    obtain ⟨same, _⟩ := callee_outcome fixture root chosen captured prefixContext history evidence stored lookup known (.fault child.sound)
    cases same
  | notCallable child invalid _ =>
    obtain ⟨same, _⟩ := callee_outcome fixture root chosen captured prefixContext history evidence stored lookup known (.value child.sound)
    cases Dynamic.ExpressionOutcome.value.inj same
    exact False.elim (invalid trivial)
  | argumentsFault first _ failed _ _ =>
    obtain ⟨same, heaps⟩ := callee_outcome fixture root chosen captured prefixContext history evidence stored lookup known (.value first.sound)
    cases Dynamic.ExpressionOutcome.value.inj same
    subst heaps
    exact False.elim (SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes.noFault fixture _ _ _ failed)
  | sourceArity _ _ mismatch _ _ => exact False.elim (mismatch rfl)
  | argumentCoercionFault _ _ _ _ failed _ _ _ =>
    change SourceExecutionSize.CoercionPathFaults _ _ _ _ _ [] _ _ _ at failed
    cases failed
  | applied _ first args packed converted unpacked sourceArity appliedArity called calleeSmall argsSmall _ callSmall =>
    obtain ⟨same, heaps⟩ := callee_outcome fixture root chosen captured prefixContext history evidence stored lookup known (.value first.sound)
    cases Dynamic.ExpressionOutcome.value.inj same
    subst heaps
    obtain ⟨valuesEq, heapEq⟩ := SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes.values_at fixture args
    subst heapEq
    change SourceExecutionSize.CoercionPathExecutes _ _ _ _ _ [] _ _ _ at converted
    cases converted
    have argumentsEq := Dynamic.ValuesPack.injective_of_length_eq packed unpacked (by
      rw [valuesEq]; exact appliedArity.symm)
    subst argumentsEq
    exact ⟨_, _, _, _, first, args, call_with_closure_evidence (.value called), calleeSmall, argsSmall, callSmall⟩
  | applicationFault first args packed converted unpacked sourceArity appliedArity called calleeSmall argsSmall _ callSmall =>
    obtain ⟨same, heaps⟩ := callee_outcome fixture root chosen captured prefixContext history evidence stored lookup known (.value first.sound)
    cases Dynamic.ExpressionOutcome.value.inj same
    subst heaps
    obtain ⟨valuesEq, heapEq⟩ := SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes.values_at fixture args
    subst heapEq
    change SourceExecutionSize.CoercionPathExecutes _ _ _ _ _ [] _ _ _ at converted
    cases converted
    have argumentsEq := Dynamic.ValuesPack.injective_of_length_eq packed unpacked (by
      rw [valuesEq]; exact appliedArity.symm)
    subst argumentsEq
    exact ⟨_, _, _, _, first, args, call_with_closure_evidence (.fault called), calleeSmall, argsSmall, callSmall⟩

include atHeader shape typing inventory captured prefixContext history extension environments heaps locals agrees typed stored lookup admitted in
/-- The original whole Source parent runs its initialized callee, one admitted
ordered argument sequence and the literal application. The result retains the
actual restored caller pool and successful Source admission. -/
theorem preserves_parent_at_initialized (budget : Nat)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size localContext evidence (source fixture.packet.named) environment before
      (expressionId fixture.packet 5) outcome after)
    (within : size ≤ budget) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates actual store (fixture.calls.parent.expression.rename ξ) result finalStore ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt
        (context := localContext) (registry := registry) (faults := faults)
        bridge functions chosen.parent.compiler initial outcome after result finalStore finalMap finalWorld := by
  obtain ⟨knownSize, known, calleePost, _selection, _stored⟩ :=
    SourceCoreChosenOrdinaryAcceptedParentEntryReceipts.callee_at_parent fixture atHeader root chosen
      bridge typing inventory evidence extension environments heaps locals agrees stored lookup initial admitted
  obtain ⟨calleeSize, argumentsSize, callSize, arguments, _actualCallee, argumentsTrace, called,
      _calleeSmall, argumentsSmall, callSmall⟩ :=
    called_at_parent fixture root chosen captured prefixContext history evidence stored lookup known trace
  obtain ⟨pair, codes, tree, childPreserves, _childReflects⟩ :=
    SourceCoreChosenOrdinaryAcceptedParentEntryReceipts.pair_at_chosen_parent fixture atHeader root chosen
      bridge functions typing evidence (registry := registry) (faults := faults)
  obtain ⟨dispatchReceipt⟩ := CallableIndexedOwnedChosenOrdinaryCallDispatchSourceTransport.at_chosen_parent
    root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
    chosen.parent.compiler chosen.parent.prepared (congrArg source atHeader.named.symm) stored.1
  let dispatch : CallStageBoundary.Dispatch (CallableLedger.frame dispatchReceipt.sidecar) chosen.parent.prepared.site
      chosen.parent.prepared.site.call [expressionId fixture.packet 6] (.closure (index).function)
      (value (index).code (index).captured.embedding history.native (index).capturedActual) :=
    ⟨dispatchReceipt.dispatch.function, dispatchReceipt.dispatch.contract, dispatchReceipt.dispatch.row,
      dispatchReceipt.dispatch.guard, dispatchReceipt.dispatch.shape, dispatchReceipt.dispatch.found,
      dispatchReceipt.dispatch.attached, dispatchReceipt.dispatch.call_eq.trans chosen.parent.prepared.call.symm,
      dispatchReceipt.dispatch.arguments_eq, dispatchReceipt.dispatch.stages, dispatchReceipt.dispatch.bound⟩
  have selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected dispatchReceipt.sidecar
      chosen.parent.prepared.site (expressionId fixture.packet 9) [expressionId fixture.packet 6]
      indirectMetadata chosen.parent.compiler.original dispatch.row := by
    simpa only [dispatch] using dispatchReceipt.selected
  obtain ⟨calleeEvaluation, represented, calleeHeaps, calleeMaps, calleeWorlds,
    calleeFrame, calleeMetadata, calleeState, calleeRelated, calleePostAdmission⟩ := calleePost
  let calleeNative := value (index).code (index).captured.embedding history.native (index).capturedActual
  have layout : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ))
      canonical (.unit :: calleeNative :: actual) :=
    GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees calleeNative) .unit
  have actualTyped := RuntimeEnvironmentHasTypes.cons RuntimeValueHasType.unit
    (RuntimeEnvironmentHasTypes.cons represented.runtime_hasType (typed.weaken calleeWorlds))
  have argumentTyping : ExpressionsHaveTypes (source fixture.packet.named) localContext
      [expressionId fixture.packet 6] [parameterType] :=
    .cons (SourceCoreChosenOrdinaryAcceptedOuterTyping.argument_typed typing) (.nil _)
  have actualTree : DataExpressionSequence.Tree (source fixture.packet.named)
      (SourceCoreChosenOrdinaryAcceptedPairArgumentBounds.Tuple fixture
        (SourceCoreChosenOrdinaryAcceptedParentEntryReceipts.fixture_root fixture atHeader root) pair)
      parentScope [expressionId fixture.packet 6] [parameterType] chosen.parent.compiler.codes := by
    rw [codes]
    exact tree
  obtain ⟨payloads, argumentStore, argumentMap, argumentWorld, argumentEvaluation, values, argumentHeaps,
      maps, worlds, frame, metadata, argumentState, argumentRelated, argumentAdmission⟩ :=
    CallableIndexedOwnedAdmittedExpressionSequence.preserves_values_bounded bridge budget actualTree
      fixture.runtime.source_runtime.graph.nodeOccurrencesUnique argumentTyping (fun childSize _ => childPreserves childSize)
      (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) layout actualTyped
      calleeState calleePostAdmission.at_value.2 argumentsTrace (Nat.le_trans (Nat.le_of_lt argumentsSmall) within)
  have arity : (index).function.parameters.length = arguments.length := by
    change (chosen.chosen.formation.function []).parameters.length = arguments.length
    rw [(SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader chosen.chosen []).1,
      shape.parameters, (SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes.values_at fixture argumentsTrace).1]
    rfl
  have rawBundle : TypeSystem.Ty.productMany [parameterType] =
      TypeSystem.Ty.productMany ((index).function.parameters.map (fun binder => binder.scheme.body)) := by
    change TypeSystem.Ty.productMany [parameterType] = TypeSystem.Ty.productMany ((chosen.chosen.formation.function []).parameters.map (fun binder => binder.scheme.body))
    rw [(SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader chosen.chosen []).1,
      shape.parameters]
    simp only [List.map_cons, List.map_nil, shape.scheme, TypeSystem.Scheme.mono]
  have parameterValues := CallableIndexedOwnedChosenOrdinaryArgumentBundles.arguments_at_compiler
    root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) stored.1 chosen.parent.compiler
    functions represented rfl inventory.contracts maps worlds values arity rawBundle
  have nativeResult := (CallableIndexedOwnedChosenOrdinaryArgumentBundles.compiler_parameters
    root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) stored.1 chosen.parent.compiler
    functions represented rfl).2
  have member := stored.1
  cases member with
  | ordinary owner _factory origin _prefix observed referenceIndex _nativeTyped =>
    have reference : captured.canonical[(index).code.referenceIndex]? =
        some (.cellRef fixture.packet.compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact observed.reference
    obtain ⟨result, finalStore, finalMap, finalWorld, application, resultPost⟩ :=
      SourceCoreChosenOrdinaryAcceptedLiteralStoredApplication.application_preserves fixture atHeader shape typing
        chosen.chosen root chosen.factory bridge functions owner (captured.extend maps worlds) prefixContext history
        origin observed argumentState argumentAdmission argumentHeaps parameterValues reference argumentsTrace
        chosen.parent.compiler chosen.parent.prepared dispatch rfl selected
        budget called (Nat.le_trans (Nat.le_of_lt callSmall) within)
    have accepted := (SourceCoreChosenOrdinaryAcceptedLiteralCallGuard.accepted_at_selected
      fixture shape atHeader chosen.chosen dispatch selected
      fixture.packet.compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown).first
    have read : Evaluates (calleeNative :: actual) store (.second (.var 0))
        (.word dispatch.contract) store :=
      .second (.var (by simpa only [List.getElem?_cons_zero] using congrArg some dispatch.shape))
    have gate := chosen.parent.prepared.site.dispatch_known .beforeArguments
      fixture.packet.compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
      dispatch.contract dispatch.row dispatch.found read
    rw [SourceCoreCallableContracts.reason_accepted dispatch.row
      chosen.parent.prepared.site.reasonAt .beforeArguments accepted] at gate
    rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at argumentEvaluation
    have whole : Evaluates actual store
        (CallableContract.call chosen.parent.prepared.site.gates
          fixture.packet.compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
          chosen.parent.compiler.resultType (chosen.parent.compiler.calleeCode.expression.rename ξ)
          ((SourceCoreCalls.packArguments chosen.parent.compiler.codes).expression.rename ξ)) result finalStore :=
      LanguageResult.bind_success _ calleeEvaluation
        (LanguageResult.bind_success _ gate (LanguageResult.bind_success _ argumentEvaluation application))
    rw [← chosen.parent.prepared.lowered_rename chosen.parent.compiler ξ] at whole
    obtain ⟨resultRep, lastHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata,
      _nested, _nestedRelated⟩ := resultPost.1
    obtain ⟨returned, returnedRelated, returnedAdmission⟩ := resultPost.2
    have rawResult : SourceCoreRawMetadata.runtimeType chosen.parent.compiler.original.type =
        SourceCoreRawMetadata.runtimeType (index).function.resultType := by
      change SourceCoreRawMetadata.runtimeType chosen.parent.compiler.original.type =
        SourceCoreRawMetadata.runtimeType (chosen.chosen.formation.function []).resultType
      rw [chosen.parent.original, fixture.graph.parentType,
        (SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader chosen.chosen []).2.1]
    have parentRep := CallableIndexedOwnedStoredIndirectCallBounds.ForModel.parent_result functions
      chosen.parent.compiler rawResult nativeResult resultRep
    have parentAdmission : PostAdmission bridge localContext chosen.parent.compiler.original.type outcome returned := by
      rw [chosen.parent.original, fixture.graph.parentType]
      exact returnedAdmission
    exact ⟨result, finalStore, finalMap, finalWorld, whole, parentRep, lastHeaps,
      (calleeMaps.trans maps).trans lastMaps, (calleeWorlds.trans worlds).trans lastWorlds,
      (calleeFrame.trans frame).trans lastFrame, (calleeMetadata.trans metadata).trans lastMetadata,
      returned, callerProtocol.trans (callerProtocol.trans calleeRelated argumentRelated) returnedRelated, parentAdmission⟩

end Tests.SourceCoreChosenOrdinaryAcceptedParentPreservationBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedParentReflectionBounds
/-! The accepted whole indirect parent uses its original initialized callee,
pair argument and stored lambda application. Actual intermediate posts are
composed at the same reached states; initial heap and stored-cell authority
remain genuine inputs. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedParentReflectionBounds
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  (atHeader : HeaderAt fixture caller)
  (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
  (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt fixture root)

universe u
variable {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures fixture.packet.compiled.indexed mapping world (initialScope fixture.packet)
    (chosen.chosen.formation.function []).captured capturedActual)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial fixture.packet.compiled.compatible.checked) caller)


variable {history : History ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).code}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
  {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
  {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location}
  (initial : callerProtocol.State ⟨(SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture), mapping, world, heap, store, canonical⟩)

include atHeader in
/-- Compose the genuine argument and application posts. This finite helper
only projects retained witnesses and does not execute or restore a second time. -/
private theorem result_at_parent
    {middleMap finalMap : LocationMap} {middleWorld finalWorld : StoreTyping}
    {middle after : Dynamic.Heap} {argumentStore finalStore : Store}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    (argumentState : callerProtocol.State ⟨(SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture), middleMap, middleWorld, middle, argumentStore, canonical⟩)
    (related : callerProtocol.Relates initial argumentState)
    (maps : LocationMap.Extends mapping middleMap) (worlds : WorldExtends world middleWorld)
    (frame : AdministrativePreserved mapping store middleMap argumentStore)
    (metadata : Dynamic.HeapMetadataExtend heap middle)
    (nativeResult : (chosen.parent.compiler).resultType = ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).code.receipt.resultCore)
    (result : CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt
      (registry := registry) (faults := faults) (((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).captured.extend maps worlds) ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).code (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts)
      (bridge.pool argumentState) outcome after value finalStore finalMap finalWorld)
    (returned : callerProtocol.State ⟨(SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture), finalMap, finalWorld, after, finalStore, canonical⟩)
    (returnedRelated : callerProtocol.Relates argumentState returned)
    (post : PostAdmission bridge (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) wordType outcome returned) :
    CallableIndexedOwnedStoredIndirectCallBounds.ForModel.ResultAt (registry := registry) (faults := faults)
      (context := (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)) bridge (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts) chosen.parent.compiler initial outcome after value finalStore finalMap finalWorld := by
  have rawType : (chosen.parent.compiler).original.type = wordType := by
    rw [chosen.parent.original, fixture.graph.parentType]
  have resultType : ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).function.resultType = wordType :=
    (SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader chosen.chosen []).2.1
  have rawResult : SourceCoreRawMetadata.runtimeType (chosen.parent.compiler).original.type =
      SourceCoreRawMetadata.runtimeType ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).function.resultType := by rw [rawType, resultType]
  obtain ⟨represented, heaps, finalMaps, finalWorlds, finalFrame, finalMetadata, _reached, _related⟩ := result
  unfold CallableIndexedOwnedStoredIndirectCallBounds.ForModel.ResultAt
  refine ⟨CallableIndexedOwnedStoredIndirectCallBounds.ForModel.parent_result (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts) chosen.parent.compiler
      rawResult nativeResult represented, heaps, maps.trans finalMaps, worlds.trans finalWorlds,
    frame.trans finalFrame, metadata.trans finalMetadata, returned,
    callerProtocol.trans related returnedRelated, ?_⟩
  simpa only [rawType] using post

variable
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial fixture.packet.compiled.compatible.checked).registry registry)
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog fixture.packet.compiled.compatible.checked.catalog)
    mapping world administrative (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture)
    environment canonical fixture.packet.compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts)
    mapping world heap store)
  (locals : Dynamic.EnvironmentAgrees heap ((SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)).locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext fixture.packet.compiled.indexed.layouts.definitions)
  (stored : CallableIndexedOwnedChosenOrdinaryStoredMembers.ChosenStoredAt root.root
    (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults
    (CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext) history heap store location)
  (lookup : Dynamic.Environment.LooksUp environment fixture.graph.binder.id location)
  (admitted : Admission bridge (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) initial)

include atHeader shape typing extension environments heaps locals agrees typed stored lookup admitted in
/-- Whole Core completion reflects to the independent Source parent and the
same admitted returned caller. Callee execution, argument meanings, guards,
dispatch and native parameter alignment are derived inside this proof. -/
theorem reflects_parent_at_initialized (budget : Nat)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (fixture.calls.parent.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
        sourceSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named) environment heap
        (expressionId fixture.packet 5) outcome after ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ForModel.ResultAt (registry := registry) (faults := faults)
        (context := (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)) bridge (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts) chosen.parent.compiler initial
        outcome after value finalStore finalMap finalWorld := by
  obtain ⟨pair, sameCodes, argumentTree, _preserves, reflects⟩ :=
    SourceCoreChosenOrdinaryAcceptedParentEntryReceipts.pair_at_chosen_parent
      fixture atHeader root chosen bridge (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts) typing evidence (registry := registry) (faults := faults)
  have tree : DataExpressionSequence.Tree (source fixture.packet.named)
      (SourceCoreChosenOrdinaryAcceptedPairArgumentBounds.Tuple fixture
        (SourceCoreChosenOrdinaryAcceptedParentEntryReceipts.fixture_root fixture atHeader root) pair)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture)
      [expressionId fixture.packet 6] [parameterType] (chosen.parent.compiler).codes := by
    simpa only [sameCodes] using argumentTree
  have argumentsTyped : ExpressionsHaveTypes (source fixture.packet.named) (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
      [expressionId fixture.packet 6] [parameterType] :=
    .cons (SourceCoreChosenOrdinaryAcceptedOuterTyping.argument_typed typing) (.nil _)
  obtain ⟨calleeSize, calleeTrace, calleePost, _selected, _stored⟩ :=
    SourceCoreChosenOrdinaryAcceptedParentEntryReceipts.callee_at_parent fixture atHeader root chosen
      bridge typing inventory evidence extension environments heaps locals agrees stored lookup initial admitted
  obtain ⟨selection⟩ := CallableIndexedOwnedChosenOrdinaryCallDispatchSourceTransport.at_chosen_parent
    root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
    chosen.parent.compiler chosen.parent.prepared (congrArg source atHeader.named).symm stored.1
  let dispatch : CallStageBoundary.Dispatch (CallableLedger.frame selection.sidecar)
      (chosen.parent.prepared).site (chosen.parent.prepared).site.call [expressionId fixture.packet 6]
      (.closure ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).function) (CallableIndexedLambdaValues.value ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).code
        ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).captured.embedding history.native ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).capturedActual) := {
    function := selection.dispatch.function, contract := selection.dispatch.contract,
    row := selection.dispatch.row, guard := selection.dispatch.guard,
    shape := selection.dispatch.shape, found := selection.dispatch.found,
    attached := selection.dispatch.attached,
    call_eq := selection.dispatch.call_eq.trans chosen.parent.prepared.call.symm,
    arguments_eq := selection.dispatch.arguments_eq, stages := selection.dispatch.stages,
    bound := selection.dispatch.bound }
  have accepted := SourceCoreChosenOrdinaryAcceptedLiteralCallGuard.accepted_at_selected
    fixture shape atHeader chosen.chosen dispatch selection.selected
    fixture.packet.compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
  have parameters := CallableIndexedOwnedChosenOrdinaryArgumentBundles.compiler_parameters
    root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) stored.1
    chosen.parent.compiler (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts) calleePost.2.1 rfl
  obtain ⟨_original, step, _passed⟩ := CallableIndexedOwnedStoredIndirectPurePrefixBounds.reflects_parent
    bridge (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts) chosen.parent.compiler chosen.parent.prepared tree fixture.runtime.source_runtime.graph.nodeOccurrencesUnique
    argumentsTyped environments locals agrees typed initial calleePost dispatch selection.selected accepted
    (SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes.noFault fixture) calleeTrace budget
    (fun size _ => reflects size) completed within
  obtain ⟨owner, _factory, origin, _prefix, globals, referenceIndex, _nativeTyped⟩ := stored.1
  have reference : ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).captured.canonical[((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).code.referenceIndex]? =
      some (.cellRef fixture.packet.compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [referenceIndex]
    exact globals.reference
  obtain ⟨_nativeSize, argumentsSize, arguments, payloads, middle, argumentStore, middleMap, middleWorld,
    _argumentsNative, _argumentsStrict, argumentsTrace, values, argumentHeaps, stepMaps, stepWorlds,
    _stepFrame, _stepMetadata, cumulativeMaps, cumulativeWorlds, cumulativeFrame, cumulativeMetadata,
    ⟨argumentState, related, argumentAdmission⟩, remainingSize, remaining, remainingStrict⟩ := step
  let current := (CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext).captured.extend stepMaps stepWorlds
  have arity : (CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext).function.parameters.length = arguments.length := by
    change (chosen.chosen.formation.function []).parameters.length = arguments.length
    rw [(SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader chosen.chosen []).1,
      shape.parameters, (SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes.values_at fixture argumentsTrace).1]
    rfl
  have rawBundle : TypeSystem.Ty.productMany [parameterType] =
      TypeSystem.Ty.productMany ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext).function.parameters.map (fun binder => binder.scheme.body)) := by
    change TypeSystem.Ty.productMany [parameterType] = TypeSystem.Ty.productMany ((chosen.chosen.formation.function []).parameters.map (fun binder => binder.scheme.body))
    rw [(SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader chosen.chosen []).1,
      shape.parameters]
    simp only [List.map_cons, List.map_nil, shape.scheme, TypeSystem.Scheme.mono]
  have actualArguments := CallableIndexedOwnedChosenOrdinaryArgumentBundles.arguments_at_compiler
    root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) stored.1 chosen.parent.compiler
    (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts)
    calleePost.2.1 rfl inventory.contracts stepMaps stepWorlds values arity rawBundle
  obtain ⟨callSize, outcome, after, finalMap, finalWorld, called, result⟩ :=
    SourceCoreChosenOrdinaryAcceptedLiteralStoredApplication.application_reflects
      (registry := registry) (faults := faults)
      (atHeader := atHeader) (shape := shape) (typing := typing) (receipt := chosen.chosen)
      (root := root) (chosen := chosen.factory) (bridge := bridge)
      (functions := CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
        (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts)
      (owner := owner) (captured := current) (prefixContext := rfl) (history := history)
      (origin := origin) (observed := globals) (argumentState := argumentState) (admitted := argumentAdmission)
      (heaps := argumentHeaps) (represented := actualArguments) (reference := reference)
      (argumentsTrace := argumentsTrace) (compiler := chosen.parent.compiler) (prepared := chosen.parent.prepared)
      (dispatch := dispatch) (sameNative := rfl) (selected := selection.selected)
      fixture budget remaining (Nat.le_of_lt remainingStrict)
  obtain ⟨sourceSize, parentTrace⟩ := SourceCoreChosenOrdinaryAcceptedLiteralStoredApplication.parent_source
    fixture chosen.chosen calleeTrace argumentsTrace called
  obtain ⟨applicationResult, returned, returnedRelated, post⟩ := result
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, parentTrace,
    result_at_parent fixture atHeader inventory root chosen bridge captured prefixContext initial
      argumentState related cumulativeMaps cumulativeWorlds cumulativeFrame cumulativeMetadata parameters.2
      applicationResult returned returnedRelated post⟩

end Tests.SourceCoreChosenOrdinaryAcceptedParentReflectionBounds
end

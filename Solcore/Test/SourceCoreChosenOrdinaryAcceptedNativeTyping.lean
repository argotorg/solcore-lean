import Solcore.Test.SourceCoreChosenOrdinaryAcceptedLiteralInputs

/-! The actual initializer is typed before any Produced or Site is selected.
Its accepted lambda certificate retains the original parameter compiler,
literal body callback, allocation, snapshot and callable descriptor. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedLambdaCertificates
open CallableIndexedParameterNativeTyping CallableIndexedLambdaScalarNativeTyping
open CallableIndexedOwnedLiteralReturnSiteShells

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
    (atHeader : HeaderAt fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (metadata : SourceCoreChosenOrdinaryAcceptedBodyMetadata.Receipt fixture.packet fixture.graph)
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation fixture.packet.compiled.indexed caller.named diagnostics namedCode}
    {fuel : Nat} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (root : LiteralRootReceipt (compiled := fixture.packet.compiled) caller.named diagnostics namedCode compilation
      fuel (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1) reasonAt lowered)

/-- This is the original body recipe at its retained recursive callback. -/
def loopPolicy : SourceCoreLoops.Policy :=
  let actual := (representation fixture.packet.compiled.indexed).atContext caller.named.signature.key []
  {actual.loopsWithSourceCells actual.expressions.sourceCells
    (context fixture.packet.compiled.indexed caller.named).solvedRequirements compilation.own.assignments diagnostics
    (context fixture.packet.compiled.indexed caller.named).owner
    (FunctionCode.children root.root.selected.policy root.root.selected.lowerBody fuel
      (context fixture.packet.compiled.indexed caller.named)) with
    sourceCells := actual.expressions.sourceCells
    lowerBinder := SourceCoreGeneralFunctions.contextualBinder actual
      fixture.packet.compiled.indexed.base.locals caller.named.signature.key []}

theorem body_callback :
    root.root.selected.lowerBody
      (FunctionCode.children root.root.selected.policy root.root.selected.lowerBody fuel
        (context fixture.packet.compiled.indexed caller.named)) =
      SourceCoreLoops.lowerStatementsWithPolicy (loopPolicy fixture root) := by
  dsimp only [loopPolicy]
  rw [root.root.selected.recipe]
  rfl

private theorem descriptor_exists (table : SourceCoreStageCodebook.Table)
    {origin : SourceCoreStageCodebook.Origin} {id : Word}
    (selected : table.idAt? origin = some id) :
    Nonempty (SourceCoreCallableContracts.Descriptor table origin) := by
  cases accepted : SourceCoreCallableContracts.descriptor table origin with
  | error error =>
    unfold SourceCoreCallableContracts.descriptor at accepted
    split at accepted
    · rename_i absent
      rw [selected] at absent
      cases absent
    · cases accepted
  | ok actual => exact ⟨actual⟩

private theorem singleton_bindings (bindings : List CallableIndexedParameterCertificates.Binding)
    (parameter : TypedBinder) (same : bindings.map Prod.fst = [parameter]) :
    ∃ type, bindings = [(parameter, type)] := by
  cases bindings with
  | nil => cases same
  | cons head tail =>
    cases tail with
    | nil =>
      have first := (List.cons.inj same).1
      exact ⟨head.2, congrArg (fun binding => [binding]) (Prod.ext first rfl)⟩
    | cons next rest =>
      have impossible := (List.cons.inj same).2
      cases impossible

private theorem final_frame (parameter frame : Ty) (globals : Core.Context) :
    (parameter :: globals ++ [.cell frame])[1 + globals.length]? = some (.cell frame) := by
  rw [Nat.add_comm 1, List.cons_append, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self, List.getElem?_cons_zero]

include shape in
/-- The real singleton parameter compiler fixes its exact native bundle. -/
theorem parameter_bundle {reported : Ty}
    (certificate : Certificate root.root.selected.policy root.root.selected.lowerBody fuel
      (context fixture.packet.compiled.indexed caller.named) (source fixture.packet.named)
      (initialScope fixture.packet) (expressionId fixture.packet 1) fixture.graph.lambdaNode
      fixture.graph.parameters wordType [statementId fixture.packet 2] reported reasonAt lowered) :
    certificate.parameterCore = packed (certificate.loweredParameters.map Prod.snd) := by
  have monomorphic : ∀ binder ∈ fixture.graph.parameters, binder.scheme.quantified = [] := by
    intro binder member
    rw [shape.parameters] at member
    have same := List.mem_singleton.mp member
    subst binder
    rw [shape.scheme]
    rfl
  have projections := parameter_projections certificate.parametersCompiled root.root.selected.binder
    (by rfl) monomorphic
  have binders := (FunctionCode.Parameters.of_accepted certificate.parametersCompiled).binders
  have binders : certificate.loweredParameters.map Prod.fst = [shape.parameter] := binders.trans shape.parameters
  obtain ⟨type, bindings⟩ := singleton_bindings _ _ binders
  have sameParameter : TypeSystem.Ty.productMany ([shape.parameter].map (·.scheme.body)) = certificate.parameter :=
    (congrArg (fun parameters : List TypedBinder => TypeSystem.Ty.productMany (parameters.map (·.scheme.body))) shape.parameters).symm.trans certificate.parameterTypes
  change shape.parameter.scheme.body = certificate.parameter at sameParameter
  have parameterProjected := CompatibleExpressionReads.projectType_of_accepted
    (root.root.projectType ▸ certificate.parameterProjected)
  have bindingProjected := CompatibleExpressionReads.projectType_of_accepted
    (projections (shape.parameter, type) (by rw [bindings]; exact List.mem_singleton_self _))
  rw [← sameParameter] at parameterProjected
  have same := Except.ok.inj (parameterProjected.symm.trans bindingProjected)
  simpa only [bindings, List.map_cons, List.map_nil, packed] using same

include atHeader shape metadata root in
/-- Native typing follows from the same accepted root and its literal body.
No Site, Produced, body meaning or native typing field is an input. -/
theorem native_at_root :
    HasType (SourceCoreLocalCell.coreContext (initialScope fixture.packet) ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) caller)
      lowered.expression (LanguageResult.resultType lowered.type) fixture.packet.compiled.indexed.layouts.definitions := by
  have found : (source caller.named).lookupExpression? (expressionId fixture.packet 1) = some fixture.graph.lambdaNode := by
    simpa only [atHeader.named] using fixture.graph.lambdaFound
  have ordinary : fixture.packet.compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context fixture.packet.compiled.indexed caller.named).owner ∧
        binding.initializer = expressionId fixture.packet 1)) = none := by
    simpa only [atHeader.named, context, CompatibleNamedBody.bodyContext] using fixture.calls.lambdaOrdinary
  have pointwise := CallableIndexedOwnedContextualCompilerPolicyProfiles.lambda_policy root.root
    (scope := initialScope fixture.packet) (reasonAt := reasonAt) fixture.graph.lambdaFound fixture.graph.lambdaForm
    fixture.graph.lambdaRequirements fixture.graph.lambdaCoercions ordinary
  have sourceEq : source caller.named = source fixture.packet.named := congrArg source atHeader.named
  have callerPointwise : CallableIndexedOwnedContextualCompilerPolicyProfiles.PointwiseFor root.root
      (source caller.named) (initialScope fixture.packet) (expressionId fixture.packet 1) reasonAt :=
    sourceEq.symm ▸ pointwise
  have accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
      (fuel + 1) (context fixture.packet.compiled.indexed caller.named) (source caller.named)
      (initialScope fixture.packet) (expressionId fixture.packet 1) reasonAt = .ok lowered := by
    exact sourceEq.symm ▸ root.root.selected.accepted
  obtain ⟨reported, read⟩ := CallableIndexedOwnedPreparedMixedBodySiteInputs.lambda_read root.root
    found fixture.graph.lambdaForm callerPointwise accepted
  have canonicalRead : SourceCoreCompatibleDataExpressions.readExpression fixture.packet.compiled.compatible.checked
      (source fixture.packet.named) (expressionId fixture.packet 1) = .ok (fixture.graph.lambdaNode, reported) :=
    sourceEq ▸ read
  have actualRead : root.root.selected.policy.readExpression (source fixture.packet.named)
      (expressionId fixture.packet 1) = .ok (fixture.graph.lambdaNode, reported) := by
    exact pointwise.read.trans canonicalRead
  have readMetadata := CompatibleExpressionReads.metadata_of_read canonicalRead
  obtain ⟨certificate⟩ := CallableIndexedLambdaCertificates.of_accepted
    (show DecoratedFunctionCode.SpecialPasses root.root.selected.policy root.root.selected.lowerBody fuel
      (context fixture.packet.compiled.indexed caller.named) (source fixture.packet.named)
      (initialScope fixture.packet) (expressionId fixture.packet 1) reasonAt from by
        exact pointwise.special _ _)
    readMetadata.owner fixture.graph.lambdaFound actualRead
    fixture.graph.lambdaForm root.root.selected.accepted
  have bodyAccepted := certificate.bodyCompiled
  rw [body_callback fixture root] at bodyAccepted
  have returnRead : (loopPolicy fixture root).readStatement (source fixture.packet.named)
      (statementId fixture.packet 2) = .ok (fixture.graph.returned, .word) := metadata.return_read
  have literalPolicy := literal_policy root.root (childSource := source fixture.packet.named)
    (childScope := certificate.bodyScope) (reasonAt := reasonAt) fixture.graph.literalFound
    (by rw [fixture.graph.literalForm]; exact .integer _ _) fixture.graph.literalOwned
    fixture.graph.literalCoercions (.inr ⟨_, _, fixture.graph.literalForm⟩)
    (by simpa only [atHeader.named, context, CompatibleNamedBody.bodyContext] using fixture.calls.literalOrdinary)
  have bodyTyped := CallableIndexedOwnedLiteralReturnLambdaStaticFacts.literal_body_native
    (show (loopPolicy fixture root).lowerExpression = FunctionCode.children root.root.selected.policy
      root.root.selected.lowerBody fuel (context fixture.packet.compiled.indexed caller.named) from rfl)
    returnRead fixture.graph.returnedForm bodyAccepted fixture.graph.literalFound
    (by rw [fixture.graph.literalForm]; exact .integer _ _)
    (by rw [fixture.graph.literalForm]; intro impossible; cases impossible)
    literalPolicy.special literalPolicy.read root.leaf fixture.packet.compiled.indexed.layouts.definitions
    (SourceCoreLocalCell.coreContext certificate.bodyScope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) caller)
  have monomorphic : ∀ binder ∈ fixture.graph.parameters, binder.scheme.quantified = [] := by
    intro binder member
    rw [shape.parameters] at member
    have same := List.mem_singleton.mp member
    subst binder
    rw [shape.scheme]
    rfl
  have projections := parameter_projections certificate.parametersCompiled root.root.selected.binder (by rfl) monomorphic
  have parameterWF := fun binding member => CompatibleExpressionReads.projectType_wellFormed (projections binding member)
  have ordinaryBindings : ∀ binding ∈ certificate.loweredParameters,
      (source fixture.packet.named).inputs.any (fun input => decide (input.id = binding.1.id)) = false := by
    intro binding member
    have belongs : binding.1 ∈ fixture.graph.parameters := by
      rw [← (FunctionCode.Parameters.of_accepted certificate.parametersCompiled).binders]
      exact List.mem_map.mpr ⟨binding, member, rfl⟩
    rw [shape.parameters] at belongs
    simpa only [List.mem_singleton.mp belongs] using shape.notInput
  have emptyScope : initialScope fixture.packet = [] := by simp only [initialScope, metadata.inputs, List.reverse_nil, List.map_nil]
  have scopeWF : ∀ binding : Resolved.LocalId × Ty, binding ∈ initialScope fixture.packet →
      binding.2.WellFormed fixture.packet.compiled.compatible.checked.catalog.definitions := by
    simp only [emptyScope, List.not_mem_nil, false_implies, implies_true]
  have current : (SourceCoreLocalCell.coreContext (initialScope fixture.packet) ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) caller)[
        (initialScope fixture.packet).length + 1 + fixture.packet.compiled.indexed.base.globals.length]? =
      some (.cell fixture.packet.compiled.indexed.ancestry.layout.frame.type) := by
    simpa only [emptyScope, SourceCoreLocalCell.coreContext, List.map_nil, List.nil_append,
      List.length_nil, Nat.zero_add, RecursiveNamedLambdaFormationHeads.nativePrefix, List.length_map] using
      final_frame caller.named.signature.parameterType fixture.packet.compiled.indexed.ancestry.layout.frame.type
        (fixture.packet.compiled.indexed.base.globals.map (·.referenceType))
  have hook := certificate.expressionHook
  rw [root.root.rawLambdaExpression] at hook
  obtain ⟨origin, _, selected, _, _, _, _, _⟩ :=
    CallableIndexedFormation.expressionHook_receipt fixture.packet.compiled.indexed.ancestry hook
  rw [(lookupExpression?_sound fixture.graph.lambdaFound).2] at selected
  obtain ⟨descriptor⟩ := descriptor_exists _ selected
  exact certificate_native fixture.packet.compiled.indexed certificate root.root.projectType root.root.sourceCells
    root.root.rawLambdaBody root.root.rawLambdaExpression root.root.callables descriptor rfl
    (parameter_bundle fixture shape root certificate) parameterWF ordinaryBindings scopeWF
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) caller)
    current bodyTyped

include atHeader shape metadata in
/-- The original initializer selector supplies this typing before the factory
receives its accepted lambda action. The parent callback remains independent. -/
theorem initializer_native
    (compilation : Compilation fixture.packet.compiled.indexed fixture.packet.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode) :
    HasType (SourceCoreLocalCell.coreContext (initialScope fixture.packet) ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) caller)
      fixture.calls.initializer.expression (LanguageResult.resultType fixture.calls.initializer.type)
      fixture.packet.compiled.indexed.layouts.definitions := by
  let original := fixture.calls.initializer_root compilation
  have actualRoot := Eq.rec
    (motive := fun (named : Named) (same : fixture.packet.named = named) =>
      LiteralRootReceipt (compiled := fixture.packet.compiled) named
        (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode
        (same ▸ compilation) 498 (source fixture.packet.named) (initialScope fixture.packet)
        (expressionId fixture.packet 1)
        ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
        fixture.calls.initializer)
    original atHeader.named.symm
  exact native_at_root fixture atHeader shape metadata actualRoot

end Tests.SourceCoreChosenOrdinaryAcceptedNativeTyping

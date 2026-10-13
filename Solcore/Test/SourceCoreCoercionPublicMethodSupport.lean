import Solcore.Test.SourceCoreCoercionPublicMethodSyntax
import Solcore.Test.SourceCoreCoercionPublicInventory
import Solcore.Test.SourceCoreCoercionPublicCatalog
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPrimitiveMethodTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionAuthority

/-! Actual operator selections retain the complete specialized method source and
its synthetic signature. The finite cached table supplies scoped syntax without
erasing the implementation substitution; SourceAt supplies independent typing. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering

structure MethodSource (fixture : CompiledFixture) (source : TypedSource) (resultType : TypeSystem.Ty) where
  function : CheckedFunction
  signature : ProgramFunctionSignature
  shape : MethodShape function signature
  sameSource : source = function.typedBody
  nodes : function.typedBody.nodes = shape.nodeList
  result : resultType = .word

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

private def observeMethodSource (fixture : CompiledFixture) (method : ExecutableImplMethods.CheckedMethod) :
    IO (MethodSource fixture method.specialized.function.typedBody method.specialized.function.inferredBodyType) := do
  let function := method.specialized.function
  let signature := method.synthetic
  let shape ← observeMethod function signature
  let ⟨result⟩ ← observed (function.inferredBodyType = .word) "coercion method result"
  let ⟨nodes⟩ ← observed (function.typedBody.nodes = shape.nodeList) "actual specialized coercion method nodes"
  return ⟨function, signature, shape, rfl, nodes, result⟩

private def MethodRowCase (fixture : CompiledFixture) (named : SourceCoreGeneralFunctions.Function) : Prop :=
  (∀ definition ∈ (Program.ofChecked fixture.recipe.compiled.sourceProgram).methods,
    named.specialized.function.typedBody.owner ≠ definition.body.source.owner) ∨
  Nonempty (MethodSource fixture named.specialized.function.typedBody named.specialized.function.inferredBodyType)

structure MethodBodies (fixture : CompiledFixture) : Prop where
  bodies : ∀ named ∈ fixture.recipe.compiled.indexed.base.functions, MethodRowCase fixture named

private def observeSelectedMethod (fixture : CompiledFixture)
    (caller : SourceSpecialization.SpecializedFunction) (node : ExpressionNode) (step : CoercionStep) :
    IO ExecutableImplMethods.CheckedMethod := do
  let available ← match SourceCompilationPlan.resolveRuntimeEvidenceEnvironment
      fixture.recipe.compiled.sourceProgram caller.key caller.assumptions with
    | .ok available => pure available
    | .error error => throw (IO.userError (reprStr error))
  match SourceCompilationPlan.checkedCoercionMethod fixture.recipe.compiled.sourceProgram caller node available step with
  | .ok method => pure method
  | .error error => throw (IO.userError (reprStr error))

private def observeMethodBodyList (fixture : CompiledFixture)
    (method : ExecutableImplMethods.CheckedMethod)
    (methodSource : MethodSource fixture method.specialized.function.typedBody method.specialized.function.inferredBodyType) :
    (named : List SourceCoreGeneralFunctions.Function) → IO (PLift (∀ row ∈ named, MethodRowCase fixture row))
  | [] => pure ⟨by intro row member; cases member⟩
  | first :: rest => do
    let ⟨head⟩ ← (do
      if nonMethod : (Program.ofChecked fixture.recipe.compiled.sourceProgram).methods.all
          (fun definition => decide (first.specialized.function.typedBody.owner ≠ definition.body.source.owner)) = true then
        return ⟨Or.inl (by intro definition member; exact of_decide_eq_true (List.all_eq_true.mp nonMethod definition member))⟩
      else if same : (first.specialized == method.specialized) = true then
        have equal : first.specialized = method.specialized := eq_of_beq same
        return ⟨Or.inr (equal ▸ ⟨methodSource⟩)⟩
      else throw (IO.userError "actual cached method specialization missing") : IO (PLift (MethodRowCase fixture first)))
    let ⟨tail⟩ ← observeMethodBodyList fixture method methodSource rest
    return ⟨by
      intro row member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail row member⟩

def observeMethodBodies (fixture : CompiledFixture) : IO (PLift (MethodBodies fixture)) := do
  let program ← observeProgram fixture
  let method ← observeSelectedMethod fixture program.makeRow.row program.makeShape.call.node program.makeShape.call.step
  let methodSource ← observeMethodSource fixture method
  let ⟨bodies⟩ ← observeMethodBodyList fixture method methodSource fixture.recipe.compiled.indexed.base.functions
  return ⟨⟨bodies⟩⟩

theorem MethodBodies.selected {fixture : CompiledFixture} (bodies : MethodBodies fixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) :
    Nonempty (MethodSource fixture principal.sourceBody.source principal.sourceBody.resultType) := by
  have member := List.mem_of_getElem? principal.cached.selected
  rcases bodies.bodies principal.named member with excluded | shape
  · obtain ⟨implementation, declaration, trait, definition, substitution, instantiated⟩ := principal.source_instantiation
    cases instantiated with
    | intro _ _ _ _ definitionMember _ _ _ _ source _ _ =>
      have selectedOwner : principal.sourceBody.source.owner = definition.body.source.owner := by
        rw [source]
        rfl
      have namedOwner : principal.named.specialized.function.typedBody.owner = principal.sourceBody.source.owner := by
        rw [principal.cached.same]
        rfl
      exact False.elim (excluded definition definitionMember (namedOwner.trans selectedOwner))
  · simpa only [principal.cached.same, CallableIndexedOwnedMethodPrincipal.Principal.sourceBody,
      CallableCoercionMethodInstantiation.bodyInstance] using shape

/-- The original selected method table has only reads, literals and a conditional. -/
theorem MethodBodies.no_lambda {fixture : CompiledFixture} (bodies : MethodBodies fixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method)
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder}
    {resultType : TypeSystem.Ty} {body : List StatementId}
    (found : principal.sourceBody.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters resultType body) : False := by
  obtain ⟨original⟩ := bodies.selected principal
  rw [original.sameSource] at found
  rcases original.shape.primitive_source original.nodes id node found with
    ⟨name, resolution, read⟩ | ⟨spelling, resolution, read⟩ | ⟨condition, first, second, read⟩ <;>
    rw [read] at form <;> cases form

/-- A terminal packet is issued from the selected cached method and its actual
compiler action. The same SourceAt receipt remains available for parameter entry. -/
theorem MethodBodies.support {fixture : CompiledFixture} (bodies : MethodBodies fixture)
    (observed : ObservedProgram fixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method)
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial fixture.recipe.compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (stages : Staging.Recursive.Registry) :
    ∃ packet : CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Packet principal,
      packet.sourceAt = sourceAt ∧
      CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Support principal packet headers stages
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  obtain ⟨original⟩ := bodies.selected principal
  have statements : principal.cached.compilation.statements = [original.shape.statement.id] := by
    have roots : (principal.sourceBody.source.roots.filterMap fun root => match root with
        | .statement statement => some statement | .expression _ => none) = principal.cached.compilation.statements :=
      principal.source_frame.roots.filterMap_eq
    rw [original.sameSource, original.shape.roots] at roots
    simpa using roots.symm
  have terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal principal.sourceBody.source
      original.shape.value.node.id principal.cached.compilation.statements := by
    have originalTerminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
        original.function.typedBody original.shape.value.node.id [original.shape.statement.id] :=
      .returning [] original.shape.statementFound original.shape.statementForm
    simpa only [original.sameSource, statements] using originalTerminal
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (by rfl) terminal sourceAt.accepted
  let packet : CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Packet principal := ⟨sourceAt, _, receipt⟩
  refine ⟨packet, rfl, ?_⟩
  apply CallableIndexedOwnedPreparedStagedPrimitiveMethodTerminalSupport.of_actual principal packet diagnostic receiver
    fixture.source_wellFormed
  · rw [original.sameSource]
    exact original.shape.primitive_source original.nodes
  · rw [original.sameSource]
    exact original.shape.metadata original.nodes principal.named observed.noLocals
  · change CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
      principal.sourceBody.source original.shape.value.node.id (fun _ => False)
    simpa only [original.sameSource] using original.shape.syntax

end Tests.SourceCoreCoercionPublic

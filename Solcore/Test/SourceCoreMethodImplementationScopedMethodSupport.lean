import Solcore.Test.SourceCoreMethodImplementationScopedMethodSyntax
import Solcore.Test.SourceCoreMethodImplementationScopedInventory
import Solcore.Test.SourceCoreMethodImplementationScopedCatalog
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodScopedRoots
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodies

/-! The original checked implementation table supplies the full local/loop
shape. Genuine empty implementation parameters fix its structural substitution;
actual SourceAt and accepted compiler receipts provide typing and execution scope. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMethodImplementationScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering

structure MethodSource (source : TypedSource) (resultType : TypeSystem.Ty) where
  function : CheckedFunction
  signature : ProgramFunctionSignature
  shape : MethodShape function signature resultType
  sameSource : source = function.typedBody
  nodes : function.typedBody.nodes = shape.nodeList

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

private def observeMethodSource (program : CheckedProgram) (method : CheckedImplementationMethod) :
    IO (MethodSource (StructuralSubstitution.applyTypedSource [] method.checked.typedBody)
      (TypeSystem.ParameterSubstitution.apply [] method.checked.inferredBodyType)) := do
  let some implementation := program.signatures.implementation? method.id.implementation
    | throw (IO.userError "method implementation missing")
  let some declaration := program.signatures.implMethod? method.id
    | throw (IO.userError "method declaration missing")
  let some trait := program.signatures.trait? declaration.traitMethod.trait
    | throw (IO.userError "method trait missing")
  let function := { method.checked with typedBody := StructuralSubstitution.applyTypedSource [] method.checked.typedBody }
  let signature := implementation.functionSignatureOfMethodWithTrait trait declaration
  let shape ← observeMethod function signature (TypeSystem.ParameterSubstitution.apply [] method.checked.inferredBodyType)
  let ⟨nodes⟩ ← observed (function.typedBody.nodes = shape.nodeList) "method original substituted nodes"
  return ⟨function, signature, shape, rfl, nodes⟩

structure MethodBodies (fixture : CompiledFixture) : Prop where
  catalog : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram
  bodies : ∀ definition, definition ∈ (Program.ofChecked fixture.recipe.compiled.sourceProgram).methods →
    Nonempty (MethodSource (StructuralSubstitution.applyTypedSource [] definition.body.source)
      (TypeSystem.ParameterSubstitution.apply [] definition.body.resultType))

private def observeMethodBodyList (program : CheckedProgram) : (methods : List CheckedImplementationMethod) →
    IO (PLift (∀ definition, definition ∈ methods.map MethodDefinition.ofChecked →
      Nonempty (MethodSource (StructuralSubstitution.applyTypedSource [] definition.body.source)
        (TypeSystem.ParameterSubstitution.apply [] definition.body.resultType))))
  | [] => pure ⟨by intro definition member; cases member⟩
  | first :: rest => do
    let shape ← observeMethodSource program first
    let ⟨tail⟩ ← observeMethodBodyList program rest
    return ⟨by
      intro definition member
      rcases List.mem_cons.mp member with same | member
      · subst definition; exact ⟨shape⟩
      · exact tail definition member⟩

def observeMethodBodies (fixture : CompiledFixture) : IO (PLift (MethodBodies fixture)) := do
  let ⟨catalog⟩ ← observeMethodCatalog fixture
  let ⟨bodies⟩ ← observeMethodBodyList fixture.recipe.compiled.sourceProgram fixture.recipe.compiled.sourceProgram.methods
  return ⟨⟨catalog, bodies⟩⟩

theorem MethodBodies.selected {fixture : CompiledFixture} (bodies : MethodBodies fixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) :
    Nonempty (MethodSource principal.sourceBody.source principal.sourceBody.resultType) := by
  obtain ⟨implementation, declaration, trait, definition, substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro implementationMember _method _trait _owner member _id _bodyOwner exact _range source result _context =>
    have parameters := bodies.catalog.parameters implementation implementationMember
    have domain := exact.domain_permutation
    rw [parameters] at domain
    have empty : substitution = [] := List.map_eq_nil_iff.mp (List.perm_nil.mp domain)
    subst substitution
    obtain ⟨shape⟩ := bodies.bodies definition member
    rw [source, result]
    exact ⟨shape⟩

/-- Every original selected method expression is a read or Boolean leaf. -/
theorem MethodBodies.no_lambda {fixture : CompiledFixture} (bodies : MethodBodies fixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method)
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder}
    {resultType : TypeSystem.Ty} {body : List StatementId}
    (found : principal.sourceBody.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters resultType body) : False := by
  obtain ⟨original⟩ := bodies.selected principal
  rw [original.sameSource] at found
  rcases original.shape.leaves original.nodes id node found with ⟨name, binder, read⟩ | ⟨name, value, read⟩ <;>
    rw [read] at form <;> cases form

/-- The exact accepted method flow and real SourceAt issue the scoped packet.
No method execution is assumed by this static construction. -/
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
    (headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry) :
    ∃ packet : CallableIndexedOwnedPreparedStagedMethodBodies.Packet principal,
      packet.sourceAt = sourceAt ∧
      CallableIndexedOwnedPreparedStagedMethodBodies.Support principal packet headers stages
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  obtain ⟨original⟩ := bodies.selected principal
  have statements : principal.cached.compilation.statements = original.shape.body := by
    have roots : (principal.sourceBody.source.roots.filterMap fun root => match root with
        | .statement statement => some statement | .expression _ => none) = principal.cached.compilation.statements :=
      principal.source_frame.roots.filterMap_eq
    rw [original.sameSource, original.shape.roots] at roots
    simpa [MethodShape.body] using roots.symm
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape principal.sourceBody.source true
      principal.cached.compilation.statements := by
    rw [original.sameSource, statements]
    exact original.shape.body_shape
  have accepted := sourceAt.accepted principal.cached.compilation
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := CompatibleEncoding.bind_ok accepted
  let packet : CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport.Packet principal :=
    ⟨sourceAt, flow, generated, (Except.ok.inj returned).symm, shape⟩
  refine ⟨.scoped packet, rfl, ?_⟩
  change CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport.Support principal packet headers stages _
  have leaves : CallableIndexedOwnedPreparedStagedMethodScopedRoots.LeafSource principal.sourceBody.source := by
    rw [original.sameSource]
    exact original.shape.leaves original.nodes
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed principal.named principal.sourceBody.source (fun _ => False) := by
    rw [original.sameSource]
    exact original.shape.metadata original.nodes principal.named observed.noLocals
  apply CallableIndexedOwnedPreparedStagedMethodScopedRoots.of_actual principal packet diagnostic receiver
    fixture.source_wellFormed leaves metadata fixture.recipePrepared observed.wordRow.entryMember
  obtain ⟨final, facts, bodyTyped, _complete⟩ :=
    CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport.statements principal packet fixture.source_wellFormed
  have unique := sourceAt.unique
  rw [original.sameSource] at unique
  rw [original.sameSource, statements] at bodyTyped ⊢
  exact (original.shape.body_syntax original.nodes unique original.shape.children bodyTyped).prepared

end Tests.SourceCoreMethodImplementationScoped

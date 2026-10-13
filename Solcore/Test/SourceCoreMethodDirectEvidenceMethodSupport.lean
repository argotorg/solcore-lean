import Solcore.Test.SourceCoreMethodDirectEvidenceMethodSyntax
import Solcore.Test.SourceCoreMethodDirectEvidenceInventory
import Solcore.Test.SourceCoreMethodDirectEvidenceCatalog
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodies

/-! The original checked implementation table supplies the full local/loop
shape. Genuine empty implementation parameters fix its structural substitution;
actual SourceAt and accepted compiler receipts provide typing and execution scope. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMethodDirectEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering

structure MethodSource (fixture : CompiledFixture) (source : TypedSource) (resultType : TypeSystem.Ty) where
  function : CheckedFunction
  signature : ProgramFunctionSignature
  shape : MethodShape function signature resultType
  sameSource : source = function.typedBody
  nodes : function.typedBody.nodes = shape.nodeList
  generic : shape.generic = fixture.identitySignature
  parameter : shape.genericParameter = fixture.identityParameter
  trait : shape.trait = .declaration fixture.mark.id
  scalar : resultType = .word ∨ resultType = .bool

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

private def observeMethodSource (fixture : CompiledFixture) (method : CheckedImplementationMethod) :
    IO (MethodSource fixture (StructuralSubstitution.applyTypedSource [] method.checked.typedBody)
      (TypeSystem.ParameterSubstitution.apply [] method.checked.inferredBodyType)) := do
  let some implementation := fixture.recipe.compiled.sourceProgram.signatures.implementation? method.id.implementation
    | throw (IO.userError "method implementation missing")
  let some declaration := fixture.recipe.compiled.sourceProgram.signatures.implMethod? method.id
    | throw (IO.userError "method declaration missing")
  let some trait := fixture.recipe.compiled.sourceProgram.signatures.trait? declaration.traitMethod.trait
    | throw (IO.userError "method trait missing")
  let function := { method.checked with typedBody := StructuralSubstitution.applyTypedSource [] method.checked.typedBody }
  let signature := implementation.functionSignatureOfMethodWithTrait trait declaration
  let ⟨shape, generic, parameter, sameTrait⟩ ← observeMethod function signature
    (TypeSystem.ParameterSubstitution.apply [] method.checked.inferredBodyType)
    fixture.identitySignature fixture.identityParameter (.declaration fixture.mark.id)
  let ⟨scalar⟩ ← observed (TypeSystem.ParameterSubstitution.apply [] method.checked.inferredBodyType = .word ∨
    TypeSystem.ParameterSubstitution.apply [] method.checked.inferredBodyType = .bool) "method scalar result"
  let ⟨nodes⟩ ← observed (function.typedBody.nodes = shape.nodeList) "method original substituted nodes"
  return ⟨function, signature, shape, rfl, nodes, generic, parameter, sameTrait, scalar⟩

structure MethodBodies (fixture : CompiledFixture) : Prop where
  catalog : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram
  bodies : ∀ definition, definition ∈ (Program.ofChecked fixture.recipe.compiled.sourceProgram).methods →
    Nonempty (MethodSource fixture (StructuralSubstitution.applyTypedSource [] definition.body.source)
      (TypeSystem.ParameterSubstitution.apply [] definition.body.resultType))

private def observeMethodBodyList (fixture : CompiledFixture) : (methods : List CheckedImplementationMethod) →
    IO (PLift (∀ definition, definition ∈ methods.map MethodDefinition.ofChecked →
      Nonempty (MethodSource fixture (StructuralSubstitution.applyTypedSource [] definition.body.source)
        (TypeSystem.ParameterSubstitution.apply [] definition.body.resultType))))
  | [] => pure ⟨by intro definition member; cases member⟩
  | first :: rest => do
    let shape ← observeMethodSource fixture first
    let ⟨tail⟩ ← observeMethodBodyList fixture rest
    return ⟨by
      intro definition member
      rcases List.mem_cons.mp member with same | member
      · subst definition; exact ⟨shape⟩
      · exact tail definition member⟩

def observeMethodBodies (fixture : CompiledFixture) : IO (PLift (MethodBodies fixture)) := do
  let ⟨catalog⟩ ← observeMethodCatalog fixture
  let ⟨bodies⟩ ← observeMethodBodyList fixture fixture.recipe.compiled.sourceProgram.methods
  return ⟨⟨catalog, bodies⟩⟩

theorem MethodBodies.selected {fixture : CompiledFixture} (bodies : MethodBodies fixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) :
    Nonempty (MethodSource fixture principal.sourceBody.source principal.sourceBody.resultType) := by
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

/-- The original selected method table has references and genuine declaration calls. -/
theorem MethodBodies.no_lambda {fixture : CompiledFixture} (bodies : MethodBodies fixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method)
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder}
    {resultType : TypeSystem.Ty} {body : List StatementId}
    (found : principal.sourceBody.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters resultType body) : False := by
  obtain ⟨original⟩ := bodies.selected principal
  rw [original.sameSource] at found
  rcases original.shape.direct_source original.nodes id node found with ⟨name, binder, read⟩ | ⟨name, value, instantiation, read⟩ <;>
    rw [read] at form <;> cases form

private theorem row_record {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (row : ObservedRow fixture signature) :
    SourceCompilationPlan.exactSpecialization fixture.recipe.compiled.indexed.base.plan row.row.key = .ok row.row := by
  obtain ⟨input, _same, packet, actual, _⟩ := row.issue
  have record := CallableIndexedActualNamedSourceReceipts.header_record fixture.recipe.compiled actual.header
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared,
    actual.prepared.same] at record
  exact record

private theorem retained_ordered {plan : SourceCompilationPlan.Plan}
    {row : SourceSpecialization.SpecializedFunction}
    (target : SourceCompilationPlan.exactInstantiationKey plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok row.key)
    (record : SourceCompilationPlan.exactSpecialization plan row.key = .ok row) :
    RecursiveNamedCallSelectionCertificates.Ordered plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) := by
  intro key selected selectedTarget selectedRecord
  have sameKey := Except.ok.inj (target.symm.trans selectedTarget)
  subst key
  have sameRow := Except.ok.inj (record.symm.trans selectedRecord)
  subst selected
  exact List.map_reverse

private theorem MethodSource.target {fixture : CompiledFixture} {source : TypedSource} {resultType : TypeSystem.Ty}
    (original : MethodSource fixture source resultType) (observed : ObservedProgram fixture)
    {instantiation : DeclarationInstantiation} (site : original.shape.DirectSites instantiation) :
    instantiation = CallableNamedCanonicalOrder.retainedInstantiation observed.identityWordRow.row ∨
    instantiation = CallableNamedCanonicalOrder.retainedInstantiation observed.identityBoolRow.row := by
  have exactCall : instantiation = ⟨fixture.identitySignature.id, [(fixture.identityParameter, resultType)],
      .function resultType resultType, [predicate (.declaration fixture.mark.id) resultType],
      fixture.identitySignature.parameterComptime, fixture.identitySignature.returnComptime⟩ := by
    rcases site with rfl | rfl | rfl
    all_goals simp only [original.shape.call.exact, original.shape.loopCall.exact, original.shape.finalCall.exact,
      original.generic, original.parameter, original.trait, predicate, SourceCoreEvidenceMethod.predicate]
  rcases original.scalar with word | bool
  · exact .inl (exactCall.trans (word ▸ observed.identityWordInstantiation.symm))
  · exact .inr (exactCall.trans (bool ▸ observed.identityBoolInstantiation.symm))

private theorem MethodSource.supported {fixture : CompiledFixture} {source : TypedSource} {resultType : TypeSystem.Ty}
    (original : MethodSource fixture source resultType) (observed : ObservedProgram fixture)
    {instantiation : DeclarationInstantiation} (site : original.shape.DirectSites instantiation) :
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported fixture.recipe.compiled.indexed.base.plan instantiation := by
  rcases original.target observed site with word | bool
  · rw [word]
    refine ⟨?_, retained_ordered observed.identityWordRow.target (row_record observed.identityWordRow)⟩
    intro parameter replacement member
    rw [observed.identityWordInstantiation] at member
    cases List.mem_singleton.mp member
    rfl
  · rw [bool]
    refine ⟨?_, retained_ordered observed.identityBoolRow.target (row_record observed.identityBoolRow)⟩
    intro parameter replacement member
    rw [observed.identityBoolInstantiation] at member
    cases List.mem_singleton.mp member
    rfl

private theorem MethodSource.covered {fixture : CompiledFixture} {source : TypedSource} {resultType : TypeSystem.Ty}
    (original : MethodSource fixture source resultType) (observed : ObservedProgram fixture)
    (inventory : OrdinaryInventory fixture observed)
    {instantiation : DeclarationInstantiation} (site : original.shape.DirectSites instantiation)
    (index : Nat) (signature : SourceCoreCalls.Signature)
    (target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan instantiation = .ok signature.key)
    (global : fixture.recipe.compiled.indexed.base.globals[index]? = some signature) :
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers inventory.rows,
      header.slot = index ∧ header.named.signature = signature := by
  rcases original.target observed site with word | bool
  · rw [word, observed.identityWordRow.target] at target
    obtain ⟨rfl, rfl⟩ := observed.identityWordRow.global_slot global (Except.ok.inj target).symm
    exact ⟨inventory.identityWordHeader.header, inventory.identityWord_member, inventory.identityWordSlot, inventory.identityWordSignature⟩
  · rw [bool, observed.identityBoolRow.target] at target
    obtain ⟨rfl, rfl⟩ := observed.identityBoolRow.global_slot global (Except.ok.inj target).symm
    exact ⟨inventory.identityBoolHeader.header, inventory.identityBool_member, inventory.identityBoolSlot, inventory.identityBoolSignature⟩

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
    (inventory : OrdinaryInventory fixture observed)
    (stages : Staging.Recursive.Registry) :
    ∃ packet : CallableIndexedOwnedPreparedStagedMethodBodies.Packet principal,
      packet.sourceAt = sourceAt ∧
      CallableIndexedOwnedPreparedStagedMethodBodies.Support principal packet (CallableIndexedOwnedPreparedFiniteNamedInventories.headers inventory.rows) stages
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
  change CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport.Support principal packet (CallableIndexedOwnedPreparedFiniteNamedInventories.headers inventory.rows) stages _
  have sourceForms : CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots.DirectSource principal.sourceBody.source := by
    rw [original.sameSource]
    exact original.shape.direct_source original.nodes
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed principal.named principal.sourceBody.source original.shape.DirectSites := by
    simpa only [original.sameSource] using
      (original.shape.metadata (directSites := original.shape.DirectSites) original.nodes principal.named observed.noLocals)
  apply CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots.of_actual principal packet diagnostic receiver
    fixture.source_wellFormed sourceForms (fun _ site => original.supported observed site) metadata
    inventory.rows (fun _ site index signature target global => original.covered observed inventory site index signature target global)
    bodies.catalog fixture.recipePrepared observed.wordRow.entryMember
  obtain ⟨final, facts, bodyTyped, _complete⟩ :=
    CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport.statements principal packet fixture.source_wellFormed
  have unique := sourceAt.unique
  rw [original.sameSource] at unique
  simp only [original.sameSource, statements] at bodyTyped ⊢
  exact original.shape.body_syntax original.nodes unique original.shape.children bodyTyped

end Tests.SourceCoreMethodDirectEvidence

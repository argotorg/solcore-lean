import Solcore.Test.SourceCoreMethodOwnEvidenceMethodSyntax
import Solcore.Test.SourceCoreMethodOwnEvidenceInventory
import Solcore.Test.SourceCoreMethodOwnEvidenceCatalog
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodies

/-! Actual operator selections retain the complete specialized method source and
its synthetic signature. The finite cached table supplies scoped syntax without
erasing the implementation substitution; SourceAt supplies independent typing. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMethodOwnEvidence
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

private def observeMethodSource (fixture : CompiledFixture) (method : ExecutableImplMethods.CheckedMethod) :
    IO (MethodSource fixture method.specialized.function.typedBody method.specialized.function.inferredBodyType) := do
  let function := method.specialized.function
  let signature := method.synthetic
  let ⟨shape, generic, parameter, sameTrait⟩ ← observeMethod function signature
    function.inferredBodyType fixture.identitySignature fixture.identityParameter (.declaration fixture.mark.id)
  let ⟨scalar⟩ ← observed (function.inferredBodyType = .word ∨ function.inferredBodyType = .bool) "method scalar result"
  let ⟨nodes⟩ ← observed (function.typedBody.nodes = shape.nodeList) "actual specialized method nodes"
  return ⟨function, signature, shape, rfl, nodes, generic, parameter, sameTrait, scalar⟩

private def MethodRowCase (fixture : CompiledFixture) (named : SourceCoreGeneralFunctions.Function) : Prop :=
  (∀ definition ∈ (Program.ofChecked fixture.recipe.compiled.sourceProgram).methods,
    named.specialized.function.typedBody.owner ≠ definition.body.source.owner) ∨
  Nonempty (MethodSource fixture named.specialized.function.typedBody named.specialized.function.inferredBodyType)

structure MethodBodies (fixture : CompiledFixture) : Prop where
  bodies : ∀ named ∈ fixture.recipe.compiled.indexed.base.functions, MethodRowCase fixture named

private def observeSelectedMethod (fixture : CompiledFixture)
    (caller : SourceSpecialization.SpecializedFunction) (node : ExpressionNode) :
    IO ExecutableImplMethods.CheckedMethod := do
  let available ← match SourceCompilationPlan.resolveRuntimeEvidenceEnvironment
      fixture.recipe.compiled.sourceProgram caller.key caller.assumptions with
    | .ok available => pure available
    | .error error => throw (IO.userError (reprStr error))
  let .unary operator _ := node.form | throw (IO.userError "method selector unary node")
  match SourceCompilationPlan.checkedUnaryOperatorMethod fixture.recipe.compiled.sourceProgram caller node available operator with
  | .ok selection => pure selection.method
  | .error error => throw (IO.userError (reprStr error))

private def observeMethodBodyList (fixture : CompiledFixture)
    (word bool : ExecutableImplMethods.CheckedMethod)
    (wordSource : MethodSource fixture word.specialized.function.typedBody word.specialized.function.inferredBodyType)
    (boolSource : MethodSource fixture bool.specialized.function.typedBody bool.specialized.function.inferredBodyType) :
    (named : List SourceCoreGeneralFunctions.Function) → IO (PLift (∀ row ∈ named, MethodRowCase fixture row))
  | [] => pure ⟨by intro row member; cases member⟩
  | first :: rest => do
    let ⟨head⟩ ← (do
      if nonMethod : (Program.ofChecked fixture.recipe.compiled.sourceProgram).methods.all
          (fun definition => decide (first.specialized.function.typedBody.owner ≠ definition.body.source.owner)) = true then
        return ⟨Or.inl (by intro definition member; exact of_decide_eq_true (List.all_eq_true.mp nonMethod definition member))⟩
      else if same : (first.specialized == word.specialized) = true then
        have equal : first.specialized = word.specialized := eq_of_beq same
        return ⟨Or.inr (equal ▸ ⟨wordSource⟩)⟩
      else if same : (first.specialized == bool.specialized) = true then
        have equal : first.specialized = bool.specialized := eq_of_beq same
        return ⟨Or.inr (equal ▸ ⟨boolSource⟩)⟩
      else throw (IO.userError "actual cached method specialization missing") : IO (PLift (MethodRowCase fixture first)))
    let ⟨tail⟩ ← observeMethodBodyList fixture word bool wordSource boolSource rest
    return ⟨by
      intro row member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail row member⟩

def observeMethodBodies (fixture : CompiledFixture) : IO (PLift (MethodBodies fixture)) := do
  let program ← observeProgram fixture
  let word ← observeSelectedMethod fixture program.relayWordRow.row program.relayWordShape.call.value.node
  let bool ← observeSelectedMethod fixture program.relayBoolRow.row program.relayBoolShape.call.value.node
  let wordSource ← observeMethodSource fixture word
  let boolSource ← observeMethodSource fixture bool
  let ⟨bodies⟩ ← observeMethodBodyList fixture word bool wordSource boolSource fixture.recipe.compiled.indexed.base.functions
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
    (resolved : CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller
      fixture.recipe.compiled.sourceProgram principal.named.specialized principal.dictionary)
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
  apply CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots.of_actual_with_evidence principal packet diagnostic receiver
    fixture.source_wellFormed sourceForms (fun _ site => original.supported observed site) metadata
    inventory.rows (fun _ site index signature target global => original.covered observed inventory site index signature target global)
    resolved fixture.recipePrepared observed.wordRow.entryMember
  obtain ⟨final, facts, bodyTyped, _complete⟩ :=
    CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport.statements principal packet fixture.source_wellFormed
  have unique := sourceAt.unique
  rw [original.sameSource] at unique
  simp only [original.sameSource, statements] at bodyTyped ⊢
  exact original.shape.body_syntax original.nodes unique original.shape.children bodyTyped

end Tests.SourceCoreMethodOwnEvidence

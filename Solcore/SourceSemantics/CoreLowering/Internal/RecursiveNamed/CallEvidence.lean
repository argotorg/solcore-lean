import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.GlobalInitialization
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.ExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionGeneralBuiltins
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.CoreEvaluation
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaTyping
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedLexicalWhile
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.ForIterations
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StatementContracts
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.AssignmentContracts
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionConditionals
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.NamedCallExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.BitNotStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StatePlaceAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRuntime
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StageCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSourceSelection
import Solcore.SourceSemantics.Staging.RecursiveProfile

/-!
# Recursive named rows: call evidence and builtin calls

Evidence of prepared calls and its heads, native contexts and typing of catalog expressions, header contracts, builtin call bounds and expression tree bounds.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedCallEvidence
/-! The actual authenticated direct-call branch fixes both complete dictionaries
and the physical prepared callee. These are static receipts and independent
source evidence judgments. No closed Header, body execution, native authority,
or whole compiler admission is constructed here. Full raw substitution order,
unused ledger rows and recursive evidence remain unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedCallEvidence
open Core Frontend SourceInference
open RecursiveNamedPublicSpecializationMeaning CallableCoercionExpressionCertificates
open CallableNamedMetadata (environment)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (action >>= next) = .ok value) : ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

/-- Only the real successful preparation fixes this key. No signature or
native type is used to identify an arbitrary source record. -/
private theorem prepared_key {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {row : SourceSpecialization.SpecializedFunction} {named : SourceCoreGeneralFunctions.Function}
    (accepted : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation row = .ok named) :
    named.signature.key = row.key := by
  unfold SourceCoreGeneralFunctions.prepareFunctionWithRepresentation at accepted
  obtain ⟨discarded, _, accepted⟩ := bind_ok accepted
  cases discarded
  by_cases staged : (row.function.returnComptime && !representation.allowStaged) = true
  · simp [staged, throw, bind, Except.bind] at accepted
  · simp only [staged] at accepted
    cases shape : row.function.type <;>
      simp only [shape, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted <;>
      try contradiction
    rename_i parameter result
    by_cases mismatch : result ≠ row.function.inferredBodyType
    · simp [mismatch] at accepted
    · simp only [mismatch, ↓reduceIte] at accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      cases accepted
      rfl

namespace Prepared
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {row : Specialized}
  (prepared : Prepared compiled row)

theorem signature_key : prepared.named.signature.key = row.key := by
  obtain ⟨specialized, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled prepared.selected
  have same := (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1
  exact (prepared_key accepted).trans (congrArg (·.key) (same.symm.trans prepared.same))

/-- Real parameter installation retains the exact source catalog, complete
ledger and declaration assumptions. -/
theorem context_fields {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend prepared.view.source.owner prepared.view.context prepared.view.parameters types context) :
    context.signatures = compiled.sourceProgram.signatures ∧
      context.solvedRequirements = row.function.solvedRequirements ∧ context.assumptions = row.assumptions := by
  have fields := RecursiveNamedInitialContextValidity.mono_fields extended
  simpa only [RecursiveNamedPublicSpecializationMeaning.Prepared.view, RecursiveNamedPreparedSourceFrames.view,
    RecursiveNamedSpecializationBodyFacts.bodyInstance, declarationContext, SourceSemantics.Context.withResidualTypeVariables,
    SourceSemantics.Context.withSolvedRequirements, SourceSemantics.Context.withAssumptions,
    SourceSemantics.Context.forDeclaration, SourceSemantics.Context.ofSignatures, prepared.same] using
    And.intro fields.signatures (And.intro fields.solvedRequirements fields.assumptions)
end Prepared

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {caller : Specialized}
  {project : Projector} {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child}
  {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
  {instantiation : DeclarationInstantiation} {reasonAt : ExpressionId → Word}
  {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode} {output : Lowered}
  (receipt : Direct compiled.sourceProgram project caller compilation child fuel caller.function.typedBody scope
    id callee arguments instantiation reasonAt policy node output)
  (callerPrepared : Prepared compiled caller)
  (calleePrepared : Prepared compiled receipt.selection.specialized)

/-- The actual caller resolver, including all ordered entries, agrees by the
same successful computation, rather than by its predicate keys. -/
theorem caller_dictionary : receipt.selection.available = callerPrepared.available :=
  Except.ok.inj (receipt.selection.resolved.symm.trans callerPrepared.resolved)

/-- Authentication compares every complete recursive evidence tree with the
same resolver used to prepare the actual callee view. -/
theorem callee_dictionary : receipt.selection.actual = calleePrepared.available := by
  have key := (CallableNamedMetadata.specialization_of_exact receipt.selection.selected).2
  apply calleePrepared.authenticated_dictionary
  simpa only [key] using receipt.selection.authenticated

/-- Full actual globals, the successful named preparer and the singleton
native selection identify the signature and physical cache slot together. -/
theorem native_target
    (globals : compilation.globals = compiled.indexed.base.globals) :
    receipt.native.signature = calleePrepared.named.signature ∧ receipt.native.index = calleePrepared.index := by
  have selected : compiled.indexed.base.globals[calleePrepared.index]? = some calleePrepared.named.signature := by
    rw [CallableIndexedPreparedInventories.cached_globals]
    simp only [List.getElem?_map, calleePrepared.selected, Option.map_some]
  have key : calleePrepared.named.signature.key = receipt.selection.key :=
    (Prepared.signature_key calleePrepared).trans (CallableNamedMetadata.specialization_of_exact receipt.selection.selected).2
  have member : (calleePrepared.named.signature, calleePrepared.index) ∈
      compilation.globals.zipIdx.filter (fun row => decide (row.1.key = receipt.selection.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr (globals ▸ selected), ?_⟩
    simp only [key, decide_true]
  rw [receipt.native.global] at member
  have same := List.mem_singleton.mp member
  exact ⟨(congrArg Prod.fst same).symm, (congrArg Prod.snd same).symm⟩

/-- The actual selected full metadata determines the retained record only with
its original reverse-domain receipt; order is not erased. -/
theorem retained_metadata
    (order : instantiation.parameterSubstitution.map Prod.fst =
      (receipt.selection.specialized.parameterSubstitution.map Prod.fst).reverse) :
    instantiation = CallableNamedCanonicalOrder.retainedInstantiation receipt.selection.specialized :=
  receipt.selection.metadata.retained_canonical order

/-- Source production uses exactly the two actual prepared dictionaries.
No unrelated source ledger row is required to be an ordinary assumption. -/
theorem produces {context : SourceSemantics.Context}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions) :
    Dynamic.DirectCallProducesEvidence context callerPrepared.view.evidence node.requirements node.coercions
      instantiation.predicates calleePrepared.view.evidence := by
  have actual := receipt.selection.direct_produces signatures ledger assumptions
  simpa only [caller_dictionary receipt callerPrepared, callee_dictionary receipt calleePrepared,
    RecursiveNamedPublicSpecializationMeaning.Prepared.view] using actual

/-- Independent source production selects the same complete output. The
source ledger's identity invariant fixes reached rows, including after an
actual lexical extension; it does not discard unused rows. -/
theorem agrees {context : SourceSemantics.Context} {semantic : Dynamic.EvidenceEnvironment}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (unique : RequirementIdsUnique context)
    (independent : Dynamic.DirectCallProducesEvidence context callerPrepared.view.evidence
      node.requirements node.coercions instantiation.predicates semantic) :
    semantic = calleePrepared.view.evidence := by
  have same := receipt.selection.direct_agrees ledger
    (CallableCallRequirementLayouts.singletons_of_unique ledger unique)
    (by simpa only [caller_dictionary receipt callerPrepared, RecursiveNamedPublicSpecializationMeaning.Prepared.view] using independent)
  simpa only [callee_dictionary receipt calleePrepared, RecursiveNamedPublicSpecializationMeaning.Prepared.view] using same

/-- The actual source frame supplies ledger identity and the real parameter
context. Independent program and full substitution-range validity remain
explicit; source typing is not inferred from native acceptance. -/
theorem at_frame {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures) caller.parameterSubstitution)
    (extended : MonoBindersExtend callerPrepared.view.source.owner callerPrepared.view.context
      callerPrepared.view.parameters types context) :
    Dynamic.DirectCallProducesEvidence context callerPrepared.view.evidence node.requirements node.coercions
      instantiation.predicates calleePrepared.view.evidence ∧
    ∀ semantic, Dynamic.DirectCallProducesEvidence context callerPrepared.view.evidence node.requirements node.coercions
      instantiation.predicates semantic → semantic = calleePrepared.view.evidence := by
  obtain ⟨signatures, ledger, assumptions⟩ := Prepared.context_fields callerPrepared extended
  have runtime := RecursiveNamedInitialContextValidity.runtime (callerPrepared.source_frame wellFormed range) extended wellFormed
  exact ⟨produces receipt callerPrepared calleePrepared signatures ledger (by intro goal member; simpa only [assumptions] using member),
    fun _ independent => agrees receipt callerPrepared calleePrepared ledger runtime.idsUnique independent⟩

/-- The selected callee frame uses the same full retained source instantiation
and authenticated dictionary; this is not a native body execution theorem. -/
theorem callee_frame
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures) receipt.selection.specialized.parameterSubstitution)
    (order : instantiation.parameterSubstitution.map Prod.fst =
      (receipt.selection.specialized.parameterSubstitution.map Prod.fst).reverse) :
    NamedCalls.SourceFrame (Program.ofChecked compiled.sourceProgram) instantiation
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram receipt.selection.specialized) calleePrepared.view := by
  exact Eq.mp (congrArg (fun selected => NamedCalls.SourceFrame (Program.ofChecked compiled.sourceProgram) selected
    (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram receipt.selection.specialized) calleePrepared.view)
    (retained_metadata receipt order).symm) (calleePrepared.retained_frame wellFormed range)

/-- Start at the actual authenticated `some` branch on the original caller
source. The returned receipt retains ordered callback results and full target
selection; no old ordinary Header or empty-callee premise is introduced. -/
theorem from_accepted {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (found : caller.function.typedBody.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation))
    (accepted : SourceCoreEvidence.lowerWithProjector compiled.sourceProgram project caller compilation child fuel
      caller.function.typedBody scope id reasonAt policy = .ok (some output))
    (globals : compilation.globals = compiled.indexed.base.globals)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures) caller.parameterSubstitution)
    (extended : MonoBindersExtend callerPrepared.view.source.owner callerPrepared.view.context
      callerPrepared.view.parameters types context) :
    ∃ receipt : Direct compiled.sourceProgram project caller compilation child fuel caller.function.typedBody scope
        id callee arguments instantiation reasonAt policy node output,
      ∀ calleePrepared : Prepared compiled receipt.selection.specialized,
        receipt.native.signature = calleePrepared.named.signature ∧ receipt.native.index = calleePrepared.index ∧
        Dynamic.DirectCallProducesEvidence context callerPrepared.view.evidence node.requirements node.coercions
          instantiation.predicates calleePrepared.view.evidence ∧
        ∀ semantic, Dynamic.DirectCallProducesEvidence context callerPrepared.view.evidence node.requirements node.coercions
          instantiation.predicates semantic → semantic = calleePrepared.view.evidence := by
  obtain ⟨actual⟩ := CallableCoercionExpressionCertificates.direct_of_accepted found form accepted
  refine ⟨actual, fun target => ?_⟩
  obtain ⟨signature, slot⟩ := native_target actual target globals
  obtain ⟨produced, same⟩ := at_frame actual callerPrepared target wellFormed range extended
  exact ⟨signature, slot, produced, same⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedCallEvidence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallEvidenceHeads
/-! Actual direct calls retain the full selected specialization and the same
caller and callee evidence. These static receipts are indexed by the argument
certificate; they contain no body execution or authority law. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallEvidenceHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableCoercionExpressionCertificates RecursiveNamedCatalog

variable {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program}
  {header : Header prepared values ambient.definitions program}
  {compilerProgram : CheckedProgram} {project : Projector} {caller : Specialized}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
  {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  (receipt : Direct compilerProgram project caller compilation child fuel source scope id callee arguments
    instantiation reasonAt policy node output)

structure Selected (header : Header prepared values ambient.definitions program) : Prop where
  member : header ∈ headers
  plan : compilation.plan = base.plan
  specialized : receipt.selection.specialized = header.named.specialized
  signature : receipt.native.signature = header.named.signature
  slot : receipt.native.index = header.slot
  occurrenceOrder : instantiation.parameterSubstitution.map Prod.fst =
    (receipt.selection.specialized.parameterSubstitution.map Prod.fst).reverse
  headerOrder : header.instantiation.parameterSubstitution.map Prod.fst =
    (header.named.specialized.parameterSubstitution.map Prod.fst).reverse

theorem Selected.metadata (reached : Selected receipt (headers := headers) header) :
    instantiation = header.instantiation := by
  have present : (receipt.native.signature, receipt.native.index) ∈
      compilation.globals.zipIdx.filter (fun row => decide (row.1.key = receipt.selection.key)) := by
    rw [receipt.native.global]
    simp
  have key : receipt.native.signature.key = receipt.selection.key :=
    of_decide_eq_true (List.mem_filter.mp present).2
  have target : SourceCompilationPlan.exactInstantiationKey compilation.plan header.instantiation =
      .ok receipt.selection.key := by
    rw [reached.plan, ← key, reached.signature]
    exact header.target
  have matched := CallableNamedMetadata.matches_of_exact target receipt.selection.selected
  have first := receipt.selection.metadata.retained_canonical reached.occurrenceOrder
  have second := matched.retained_canonical (by simpa only [reached.specialized] using reached.headerOrder)
  exact first.trans second.symm

theorem Selected.arity (reached : Selected receipt (headers := headers) header) :
    header.function.parameters.length = arguments.length := by
  have inputs : receipt.selection.specialized.function.typedBody.inputs = header.function.parameters := by
    rw [reached.specialized, ← header.agreement.source, header.inputs, ← header.parameters]
  simpa only [inputs] using receipt.arity.symm

/-- Raw source fields survive authenticated lowering without discarding the
requirements attached to the direct call occurrence. -/
structure RawMetadata (checked : SourceCoreCompatibleCatalog.Checked)
    (source : TypedSource) (id : ExpressionId) (node : ExpressionNode) (type : Ty) : Prop where
  found : source.lookupExpression? id = some node
  owner : id.occurrence.owner = source.owner
  coercions : node.coercions = []
  projected : checked.catalog.project node.type = .ok type

structure SourceTypes (headers : Inventory prepared values ambient.definitions program)
    (context : SourceSemantics.Context) : Prop where
  parameters : ∀ header, header ∈ headers → ∀ signature,
    signature ∈ context.signatures.functions → header.instantiation.declaration = signature.id →
    signature.parameterTypes.map (TypeSystem.ParameterSubstitution.apply header.instantiation.parameterSubstitution) =
      header.bindings.map (fun binding => binding.1.scheme.body)
  result : ∀ header, header ∈ headers → ∀ signature,
    signature ∈ context.signatures.functions → header.instantiation.declaration = signature.id →
    header.instantiation.parameterSubstitution.apply (TypeSystem.Ty.productMany signature.returnTypes) = header.function.resultType
  projections : ∀ header, header ∈ headers →
    (header.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (header.bindings.map Prod.snd)

/-- Source validity comes from this exact full Header and the original caller
binder well-formedness. No lexical or residual scope flag changes. -/
theorem header_valid {context : SourceSemantics.Context}
    (header : Header prepared values ambient.definitions program)
    (signatures : context.signatures = program.signatures)
    (binders : TypeParameterBindersWellFormed context) :
    SourceSemantics.DeclarationInstantiation.Valid context header.instantiation := by
  have supported : Dynamic.TypeContextSupports (Context.ofSignatures program.signatures) context := {
    signatures := signatures
    parameters := by intro parameter member; cases member
    parameterOwners := by intro parameter member; cases member
    variables := by intro metavariable member; cases member
    residualVariables := by intro impossible; cases impossible
    targetBinders := binders }
  cases header.frame.instantiated with
  | intro _ _ _ _ valid _ _ _ =>
    exact Dynamic.DeclarationInstantiation.Valid.transportContext supported valid

/-- The dictionary is the source evidence judgment for the actual caller,
including every retained requirement and selected callee predicate. -/
structure RawCall (context : SourceSemantics.Context) (callerEvidence : Dynamic.EvidenceEnvironment)
    (children : GenericExpressionMeaning.Certificate)
    (header : Header prepared values ambient.definitions program) where
  selected : Selected receipt (headers := headers) header
  sourceType : node.type = header.function.resultType
  calleeNode : ExpressionNode
  name : String
  calleeFound : source.lookupExpression? callee = some calleeNode
  calleeForm : calleeNode.form = .reference name (.declaration header.instantiation)
  calleeRequirements : calleeNode.requirements = []
  calleeCoercions : calleeNode.coercions = []
  valid : SourceSemantics.DeclarationInstantiation.Valid context header.instantiation
  dictionary : Dynamic.DirectCallProducesEvidence context callerEvidence node.requirements
    node.coercions instantiation.predicates header.function.evidence
  sequence : DataExpressionSequence.Tree source children scope arguments
    (header.bindings.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments
  nativeTypes : receipt.loweredArguments.map (·.type) = header.bindings.map Prod.snd

theorem RawCall.emitted {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {children : GenericExpressionMeaning.Certificate}
    (certified : RawCall receipt context callerEvidence children (headers := headers) header)
    (coercions : node.coercions = []) :
    output = ⟨header.output, SourceCoreCalls.call header.named.signature
      (scope.length + compilation.administrativePrefix + header.slot)
      (SourceCoreCalls.packArguments receipt.loweredArguments).expression compilation.internalReason⟩ := by
  have accepted := receipt.suffix.accepted
  rw [coercions] at accepted
  have same : receipt.operand = output := Except.ok.inj accepted
  exact same.symm.trans (by simpa only [certified.selected.signature, certified.selected.slot, header.resultType] using receipt.native.emitted)

/-- Ordinary and authenticated nodes share one argument Tree. The authenticated
constructor fixes the actual caller dictionary, not an arbitrary environment. -/
inductive Head (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (callerEvidence : Dynamic.EvidenceEnvironment)
    (children : GenericExpressionMeaning.Certificate) (scope : SourceCoreLocalCell.Scope) :
    ExpressionId → Lowered → Prop where
  | ordinary {id : ExpressionId} {output : Lowered}
      (head : RecursiveNamedCatalog.Head headers compilation source context children scope id output) :
      Head headers compilation source context callerEvidence children scope id output
  | direct {compilerProgram : CheckedProgram} {project : Projector} {caller : Specialized}
      {child : SourceCoreEvidence.Child} {fuel : Nat} {id callee : ExpressionId}
      {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
      {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
      {node : ExpressionNode} {output : Lowered} {header : Header prepared values ambient.definitions program}
      (receipt : Direct compilerProgram project caller compilation child fuel source scope id callee arguments
        instantiation reasonAt policy node output)
      (certified : RawCall receipt context callerEvidence children (headers := headers) header)
      (metadata : RawMetadata values.checked source id node header.output) :
      Head headers compilation source context callerEvidence children scope id output

/-- The legacy family is definitionally unchanged; the evidence family fixes
one actual source caller dictionary throughout every child occurrence. -/
def Calls (callerEvidence : Option Dynamic.EvidenceEnvironment)
    (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (source : TypedSource)
    (context : SourceSemantics.Context) :
    GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate :=
  match callerEvidence with
  | none => RecursiveNamedCatalog.Head headers compilation source context
  | some evidence => Head headers compilation source context evidence


section Bounds
open CoreProof RecursiveNamedCatalogInvocationBounds

variable {locations : RecursiveNamedCatalog.Locations}
  {capturePrefix : Nat} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {faults : FunctionCalls.FaultRep} {children : GenericExpressionMeaning.Certificate}

/-- The requirement identifiers select one dictionary for this exact caller.
Only the original argument and called-body children consume smaller budgets. -/
theorem preserves_at_for (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P)
    (catalog : ∀ {scope mapping world heap store canonical}, P scope mapping world heap store canonical →
      protectedEntry headers locations capturePrefix compilation.administrativePrefix scope mapping world heap store canonical)
    (conditions : ∀ header, BodyCondition (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header)
    (authorized : ∀ header, header ∈ headers → BodyAuthorization (headers := headers) (locations := locations)
      (capturePrefix := capturePrefix) functions registry header (conditions header))
    (budget size : Nat) (within : size ≤ budget)
    (idsUnique : RequirementIdsUnique context) (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (argumentMeaning : RecursiveNamedBoundedContracts.Below budget (fun child => RecursiveNamedBoundedContracts.PreservesAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source children faults
      P))
    (bodyMeaning : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (conditions header))) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head headers compilation source context evidence children) faults
      P := by
  intro scope id lowered head
  cases head with
  | ordinary ordinary =>
    exact RecursiveNamedExpressionHeadBounds.preserves_at_for functions P transport catalog conditions authorized budget size within unique owners argumentMeaning bodyMeaning ordinary
  | @direct compilerProgram project caller child fuel id callee arguments instantiation reasonAt policy node output header receipt certified metadata =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees typed installed trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨callerEntry⟩ := catalog installed
    have instantiationEq := certified.selected.metadata receipt
    have form : node.form = .call callee arguments (.declaration header.instantiation) := by
      simpa only [instantiationEq] using receipt.form
    have dictionary : Dynamic.DirectCallProducesEvidence context evidence node.requirements []
        header.instantiation.predicates header.function.evidence := by
      simpa only [metadata.coercions, instantiationEq] using certified.dictionary
    have independent := RecursiveNamedArgumentTraceBounds.source_inv_with_evidence metadata.found metadata.coercions
      form certified.calleeFound dictionary idsUnique unique trace
    have packed : header.named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
      simpa only [certified.selected.signature] using receipt.native.inputType
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preserved, heapMetadata, _⟩ :=
      RecursiveNamedExpressionHeadBounds.call_preserves_bounded_for functions certified.sequence certified.nativeTypes packed P transport (conditions header) (authorized header certified.selected.member) budget
        argumentMeaning (bodyMeaning header certified.selected.member) owners certified.selected.member
        callerEntry installed environments heaps locals agrees typed independent within
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, preserved, heapMetadata⟩
    · change Evaluates actual store (lowered.expression.rename ξ) value finalStore
      rw [certified.emitted receipt metadata.coercions]
      simpa only [NamedCalls.Arguments.call_rename] using evaluated
    · simpa only [certified.sourceType, (congrArg (fun code : Lowered => code.type) (certified.emitted receipt metadata.coercions))] using represented

theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (idsUnique : RequirementIdsUnique context) (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (argumentMeaning : RecursiveNamedBoundedContracts.Below budget (fun child => RecursiveNamedBoundedContracts.PreservesAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source children faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix)))
    (bodyMeaning : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head headers compilation source context evidence children) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  preserves_at_for functions _ entry_transport (fun entry => entry)
    (fun _ => fun {_ _ _ _ _ _ _ _ _ _ _ _} _ => True)
    (fun _ _ => by unfold BodyAuthorization; intros; trivial) budget size within idsUnique unique owners argumentMeaning
    (by
      intro header member child smaller arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry result after _ trace
      exact bodyMeaning header member child smaller entry trace)

/-- Reflection consumes the original completed call and its strict native
children. Its source grade and authenticated dictionary remain independent. -/
theorem reflects_at_for (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P)
    (catalog : ∀ {scope mapping world heap store canonical}, P scope mapping world heap store canonical →
      protectedEntry headers locations capturePrefix compilation.administrativePrefix scope mapping world heap store canonical)
    (conditions : ∀ header, BodyCondition (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header)
    (authorized : ∀ header, header ∈ headers → BodyAuthorization (headers := headers) (locations := locations)
      (capturePrefix := capturePrefix) functions registry header (conditions header))
    (budget size : Nat) (within : size ≤ budget)
    (argumentMeaning : RecursiveNamedBoundedContracts.Below budget (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source children faults
      P))
    (bodyMeaning : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (conditions header))) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head headers compilation source context evidence children) faults
      P := by
  intro scope id lowered head
  cases head with
  | ordinary ordinary =>
    exact RecursiveNamedExpressionHeadBounds.reflects_at_for functions P transport catalog conditions authorized budget size within argumentMeaning bodyMeaning ordinary
  | @direct compilerProgram project caller child fuel id callee arguments instantiation reasonAt policy node output header receipt certified metadata =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees typed installed evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨callerEntry⟩ := catalog installed
    have emitted := certified.emitted receipt metadata.coercions
    change EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore at evaluated
    rw [emitted] at evaluated
    simp only [NamedCalls.Arguments.call_rename] at evaluated
    have packed : header.named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
      simpa only [certified.selected.signature] using receipt.native.inputType
    obtain ⟨traceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preserved, heapMetadata, _⟩ :=
      RecursiveNamedExpressionHeadBounds.call_reflects_bounded_for functions certified.sequence certified.nativeTypes packed P transport (conditions header) (authorized header certified.selected.member) budget
        argumentMeaning (bodyMeaning header certified.selected.member) certified.selected.member
        callerEntry installed environments heaps locals agrees typed evaluated within
    have instantiationEq := certified.selected.metadata receipt
    have form : node.form = .call callee arguments (.declaration header.instantiation) := by
      simpa only [instantiationEq] using receipt.form
    have dictionary : Dynamic.DirectCallProducesEvidence context evidence node.requirements []
        header.instantiation.predicates header.function.evidence := by
      simpa only [metadata.coercions, instantiationEq] using certified.dictionary
    obtain ⟨sourceSize, independent⟩ := RecursiveNamedArgumentTraceBounds.source_intro_with_evidence metadata.found
      metadata.coercions form certified.calleeFound certified.calleeForm certified.calleeRequirements certified.calleeCoercions
      certified.valid dictionary trace
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, independent,
      by simpa only [certified.sourceType, congrArg (fun code : Lowered => code.type) emitted] using represented,
      finalHeaps, maps, worlds, preserved, heapMetadata⟩

theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (argumentMeaning : RecursiveNamedBoundedContracts.Below budget (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source children faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix)))
    (bodyMeaning : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head headers compilation source context evidence children) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  reflects_at_for functions _ entry_transport (fun entry => entry)
    (fun _ => fun {_ _ _ _ _ _ _ _ _ _ _ _} _ => True)
    (fun _ _ => by unfold BodyAuthorization; intros; trivial) budget size within argumentMeaning
    (by
      intro header member child smaller arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry result after _ trace
      exact bodyMeaning header member child smaller entry trace)

end Bounds

/-- Projection comes from the same original source metadata and actual emitted
result annotation. Native typing never supplies source authentication. -/
theorem projected {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {children : GenericExpressionMeaning.Certificate}
    (head : Head headers compilation source context evidence children scope id output)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    values.checked.catalog.project node.type = .ok output.type := by
  cases head with
  | ordinary ordinary =>
    cases ordinary with
    | named _ metadata _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      exact same ▸ metadata.projected
  | direct receipt certified metadata =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    have outputType := congrArg (fun code : Lowered => code.type) (certified.emitted receipt metadata.coercions)
    simpa only [same, outputType] using metadata.projected

/-- Only the actual selected global positions need valid native annotations.
The same ordered argument Tree types the original packed argument code. -/
theorem native_at {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions) {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {children : GenericExpressionMeaning.Certificate} {administrative : Core.Context}
    (slots : ∀ header, header ∈ headers → administrative[compilation.administrativePrefix + header.slot]? =
      some header.named.signature.referenceType)
    (head : Head headers compilation source context evidence children scope id output)
    (typed : ∀ child code, children scope child code →
      CompatibleExpressionScalarNativeTyping.NativeTyping definitions
        (SourceCoreLocalCell.coreContext scope ++ administrative) code) :
    CompatibleExpressionScalarNativeTyping.NativeTyping definitions
      (SourceCoreLocalCell.coreContext scope ++ administrative) output := by
  cases head with
  | ordinary ordinary =>
    cases ordinary with
    | @named callee arguments body node calleeNode name codes expression member metadata sourceType form calleeFound calleeForm
        calleeRequirements calleeCoercions valid predicates evidence arity emission selectedSlot sequence nativeTypes =>
      have packed := CompatibleExpressionConstructorNativeTyping.packed_native sequence typed
      have equation := emission.equation
      have resultWF := CompatibleExpressionCertificateNativeTyping.project_wellFormed metadata.projected |>.extend_definitions extension
      refine ⟨resultWF, ?_⟩
      rw [equation.1, selectedSlot]
      rw [← body.resultType]
      apply SourceCoreCalls.call_hasType compilation.internalReason
      · rw [equation.2.1]; exact packed.1
      · rw [body.resultType]; exact resultWF
      · have found := slots body member
        simpa [SourceCoreLocalCell.coreContext, List.getElem?_append, List.length_map, Nat.add_assoc] using found
      · rw [equation.2.1]; exact packed.2
  | @direct compilerProgram project caller child fuel id callee arguments instantiation reasonAt policy node output header receipt certified metadata =>
    have packed := CompatibleExpressionConstructorNativeTyping.packed_native certified.sequence typed
    have resultWF := CompatibleExpressionCertificateNativeTyping.project_wellFormed metadata.projected |>.extend_definitions extension
    rw [certified.emitted receipt metadata.coercions]
    refine ⟨resultWF, ?_⟩
    change HasType _ (SourceCoreCalls.call _ _ _ _) (LanguageResult.resultType _) _
    rw [← header.resultType]
    apply SourceCoreCalls.call_hasType compilation.internalReason
    · have parameter : header.named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
        simpa only [certified.selected.signature] using receipt.native.inputType
      rw [parameter]
      exact packed.1
    · rw [header.resultType]; exact resultWF
    · have found := slots header certified.selected.member
      simpa [SourceCoreLocalCell.coreContext, List.getElem?_append, List.length_map, Nat.add_assoc] using found
    · have parameter : header.named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
        simpa only [certified.selected.signature] using receipt.native.inputType
      rw [parameter]
      exact packed.2

theorem native {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {children : GenericExpressionMeaning.Certificate} {administrative : Core.Context}
    (slots : ∀ header, header ∈ headers → administrative[compilation.administrativePrefix + header.slot]? =
      some header.named.signature.referenceType)
    (head : Head headers compilation source context evidence children scope id output)
    (typed : ∀ child code, children scope child code →
      CompatibleExpressionScalarNativeTyping.NativeTyping values.checked.catalog.definitions
        (SourceCoreLocalCell.coreContext scope ++ administrative) code) :
    CompatibleExpressionScalarNativeTyping.NativeTyping values.checked.catalog.definitions
      (SourceCoreLocalCell.coreContext scope ++ administrative) output :=
  native_at (.refl _) slots head typed

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallEvidenceHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogNativeContexts
/-! Cached code typing is moved to the real canonical body environment using
an authenticated global inventory and a checked free-slot bound. Runtime value
types identify reference slots; the body's typing comes from the actual cached
code, not from those value types. The ordinary named capture prefix is zero.
Unused wrapper inputs remain arbitrary on both sides. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogNativeContexts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open NativeExpressionContextSupport

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}

/-- Every cached global has the same actual slot and complete signature in the
finite semantic inventory. Duplicates are not reordered or silently removed. -/
def Complete (headers : Inventory prepared values ambient.definitions program) : Prop :=
  ∀ index signature, base.globals[index]? = some signature →
    ∃ header, header ∈ headers ∧ header.slot = index ∧ header.named.signature = signature

def bodyScope (header : Header prepared values ambient.definitions program) : SourceCoreLocalCell.Scope :=
  header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))

def bodyPrefix (header : Header prepared values ambient.definitions program) : Core.Context :=
  SourceCoreLocalCell.coreContext (bodyScope header) ++
    SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) ::
    base.globals.map (·.referenceType) ++ [.cell prepared.layout.frame.type]

/-- The exact cached lambda and real marked parameter action fix the body code
and parameter types before any environment transport. -/
theorem body_of_cached {header : Header prepared values ambient.definitions program}
    {suffix : Core.Context}
    (typed : HasType (base.globals.map (·.referenceType) ++ .cell prepared.layout.frame.type :: suffix)
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType ambient.definitions) :
    HasType (bodyPrefix header ++ suffix) header.body (LanguageResult.resultType header.output) ambient.definitions := by
  cases typed with
  | lambda parameterWF resultWF codeTyped =>
    obtain ⟨_, _, _, _, emitted⟩ := CallableIndexedFormation.namedBody_receipt prepared header.hook
    rw [emitted] at codeTyped
    have parameters := CallableIndexedParameterNativeInversion.withFrame_body codeTyped
    have body := CallableIndexedParameterNativeInversion.accepted_body header.onError header.acceptedPrefix parameters
    rw [CallableIndexedParameterNativeInversion.final_context] at body
    simpa only [bodyPrefix, bodyScope, header.parameterType, header.resultType,
      List.append_assoc, List.cons_append, List.nil_append] using body

/-- Preparation supplies the native proof from its checked assembled entry.
The cached-row equation identifies the header's exact lambda. -/
theorem prepared_body {initial : SourceCoreCompatibleFunctions.Prepared checked} {fuel : Nat}
    {indexed : SourceCoreCallableIndexedPrograms.Prepared checked}
    (accepted : SourceCoreCallableIndexedPrograms.prepare initial fuel = .ok indexed)
    {entry : SourceCoreCallableIndexedPrograms.Entry indexed.layouts} (member : entry ∈ indexed.entries)
    {values : ValuesContext} {program : Program}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (definitions : ambient.definitions = indexed.layouts.definitions)
    (header : Header indexed.ancestry values ambient.definitions program)
    (cached : indexed.secondPass.closures[header.slot]? = some
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code))
    (global : indexed.base.globals[header.slot]? = some header.named.signature) :
    HasType (bodyPrefix header ++ SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
      header.body (LanguageResult.resultType header.output) ambient.definitions := by
  apply body_of_cached
  simpa only [← definitions] using CallableIndexedCachedNativeTyping.prepared_native_closure accepted member cached global

variable {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {header : Header prepared values ambient.definitions program}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}

/-- The real entry fixes every used reference type, including the shared
frame. No equality is required of the unused administrative suffix. -/
theorem entry_prefix (complete : Complete headers)
    (globals : header.globals = base.globals.length)
    (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    (suffix : Core.Context) :
    Agrees (bodyPrefix header).length (bodyPrefix header ++ suffix)
      (SourceCoreLocalCell.coreContext (bodyScope header) ++
        SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) := by
  let localTypes := SourceCoreLocalCell.coreContext (bodyScope header)
  let bundle := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd)
  have localLength : localTypes.length = header.bindings.length := by
    simp [localTypes, SourceCoreLocalCell.coreContext, bodyScope]
  have tag {index : Nat} {value : Value} (found : entry.canonical[index]? = some value) :
      (localTypes ++ bundle :: administrative)[index]? = some value.type := by
    have types := entry.environments.runtime_hasTypes.type_tags
    change entry.canonical.map Value.type = localTypes ++ bundle :: administrative at types
    rw [← types]
    simp [found]
  intro index smaller
  change (localTypes ++ bundle :: administrative)[index]? =
    (localTypes ++ bundle :: base.globals.map (·.referenceType) ++ [.cell prepared.layout.frame.type] ++ suffix)[index]?
  by_cases localSlot : index < localTypes.length
  · simp [List.getElem?_append, localSlot]
  · let offset := index - localTypes.length
    have indexEq : index = localTypes.length + offset := by omega
    rw [indexEq]
    have prefixLength : (bodyPrefix header).length = localTypes.length + base.globals.length + 2 := by simp [bodyPrefix, localTypes]; omega
    rw [prefixLength] at smaller
    have offsetBound : offset < base.globals.length + 2 := by omega
    cases offsetEq : offset with
    | zero => simp [List.getElem?_append]
    | succ slot =>
      have bound : slot < base.globals.length + 1 := by omega
      have outside : ¬ localTypes.length + (slot + 1) < localTypes.length := by omega
      by_cases globalSlot : slot < base.globals.length
      · let signature := base.globals[slot]
        have selected : base.globals[slot]? = some signature := List.getElem?_eq_some_iff.mpr ⟨globalSlot, rfl⟩
        obtain ⟨target, member, sameSlot, sameSignature⟩ := complete slot signature selected
        have found := entry.catalog.globals target member
        have idx : (bodyScope header).length + (0 + 1) + target.slot = localTypes.length + (slot + 1) := by
          simp only [bodyScope, List.length_map, List.length_reverse, localLength, sameSlot]; omega
        change entry.canonical[(bodyScope header).length + (0 + 1) + target.slot]? = _ at found
        have typed := tag found
        rw [idx] at typed
        simpa [List.getElem?_append, outside, globalSlot, selected, signature,
          sameSignature, SourceCoreCalls.Signature.referenceType, OptionalCell.referenceType, Value.type] using typed
      · have last : slot = base.globals.length := by omega
        have typed := tag entry.reference
        have idx : header.bindings.length + 1 + header.globals = localTypes.length + (slot + 1) := by omega
        rw [idx] at typed
        simpa [List.getElem?_append, outside, last, Value.type] using typed

/-- The support receipt concerns this exact emitted body. In particular,
no arbitrary administrative-context native typing is an input. -/
theorem canonical_body {suffix : Core.Context}
    (complete : Complete headers) (globals : header.globals = base.globals.length)
    (typed : HasType (bodyPrefix header ++ suffix) header.body (LanguageResult.resultType header.output) ambient.definitions)
    (support : supported header.body (bodyPrefix header).length = true)
    (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost) :
    HasType (SourceCoreLocalCell.coreContext (bodyScope header) ++
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      header.body (LanguageResult.resultType header.output) ambient.definitions :=
  typing typed support (entry_prefix complete globals entry suffix)

/-- A support check on the actual cached lambda also bounds the emitted
body. First remove only the unused wrapper suffix syntactically, then invert
the real hook and allocation actions. -/
theorem canonical_cached {suffix : Core.Context}
    (complete : Complete headers) (globals : header.globals = base.globals.length)
    (cachedTyped : HasType (base.globals.map (·.referenceType) ++ .cell prepared.layout.frame.type :: suffix)
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType ambient.definitions)
    (support : supported (.lambda header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) header.code) (base.globals.length + 1) = true)
    (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost) :
    HasType (SourceCoreLocalCell.coreContext (bodyScope header) ++
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      header.body (LanguageResult.resultType header.output) ambient.definitions := by
  have original : HasType ((base.globals.map (·.referenceType) ++ [.cell prepared.layout.frame.type]) ++ suffix)
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType ambient.definitions := by simpa using cachedTyped
  have minimal := NativeExpressionContextSupport.prefix_typing (targetSuffix := []) original (by simpa using support)
  have body := body_of_cached (suffix := []) (by simpa using minimal)
  have bodySupport : supported header.body (bodyPrefix header).length = true := by
    simpa using of_typing body
  exact canonical_body complete globals body bodySupport entry

/-- The real entry embedding transports that syntax proof to the actual
parameter environment; no captured environment or closure is rewritten. -/
theorem actual_body {suffix : Core.Context}
    (complete : Complete headers) (globals : header.globals = base.globals.length)
    (typed : HasType (bodyPrefix header ++ suffix) header.body (LanguageResult.resultType header.output) ambient.definitions)
    (support : supported header.body (bodyPrefix header).length = true)
    (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost) :
    HasType (CallableIndexedParameterTyped.prefixContext header.bindings actualContext)
      (header.body.rename entry.embedding) (LanguageResult.resultType header.output) ambient.definitions := by
  exact (canonical_body complete globals typed support entry).rename
    (TypedLexicalWhile.environment_respects entry.environments.runtime_hasTypes entry.actualTyped entry.lookups)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogNativeContexts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionNativeTyping
/-! The same call Tree types ordinary expressions and direct named calls.
Only authenticated global reference positions are required from the caller.
Callee executions, cached body meaning and runtime result typing are absent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionNativeTyping
open Core Frontend SourceInference CompatibleExpressionPrimitives
open CompatibleExpressionScalarNativeTyping CompatibleExpressionConstructorNativeTyping
open CompatibleExpressionMemberNativeTyping CompatibleExpressionDataLeafNativeTyping
open CompatibleExpressionCertificateNativeTyping CompatibleCatalogNominalCoverage
open CallableAncestryPairedLookup RecursiveNamedCatalog

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {compilation : SourceCoreFunctions.Context}

/-- Positions are relative to the administrative suffix after source locals.
Only members of this exact inventory can occur in a named call head. -/
def Slots (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (administrative : Core.Context) : Prop :=
  ∀ header, header ∈ headers →
    administrative[compilation.administrativePrefix + header.slot]? = some header.named.signature.referenceType

private theorem primitive_native {definitions : DataEnvironment} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {children : GenericExpressionMeaning.Certificate} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {context : Core.Context}
    (head : CompatibleExpressionTypedCompositions.Head values.checked source children scope id lowered)
    (typed : ∀ child code, children scope child code → NativeTyping definitions context code) :
    NativeTyping definitions context lowered := by
  cases head with
  | group _ _ _ _ child => exact typed _ _ child
  | pair _ _ _ _ _ first second =>
    have a := typed _ _ first
    have b := typed _ _ second
    exact ⟨.product a.1 b.1, LocalSequence.pair_hasType a.1 b.1 a.2 b.2⟩
  | unary _ _ _ _ _ profile child =>
    have operand := typed _ _ child
    cases profile <;> exact ⟨by constructor, LocalPrimitiveResults.unary_hasType operand.2⟩
  | binary _ _ _ _ _ _ _ _ first second => exact binary_native (typed _ _ first).2 (typed _ _ second).2
  | conditional _ _ _ _ _ _ _ _ first second third =>
    have a := typed _ _ first
    have b := typed _ _ second
    have c := typed _ _ third
    exact ⟨b.1, LocalControl.choose_hasType b.1 a.2 b.2 c.2⟩

theorem named_native {source : TypedSource} {sourceContext : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {children : GenericExpressionMeaning.Certificate}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {administrative : Core.Context}
    (slots : Slots headers compilation administrative)
    (head : RecursiveNamedCatalog.Head headers compilation source sourceContext children scope id lowered)
    (typed : ∀ child code, children scope child code →
      NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) code) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered :=
  RecursiveNamedCallEvidenceHeads.native (evidence := []) slots (.ordinary head) typed

variable {readFuel : Nat} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (shaped : Shapes values.checked.signatures values.checked.catalog) (complete : Complete values.checked.catalog)
  {administrative : Core.Context} (slots : Slots headers compilation administrative)

include shaped complete in
theorem tree_native_for {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions)
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (callTyped : ∀ {children scope id lowered}, calls children scope id lowered →
      (∀ child code, children scope child code → NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) code) →
      NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered)
    (tree : CompatibleExpressionCalls.Tree calls readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | fragment child => exact builtins_native_at administrative shaped complete extension child
  | node head _ ih =>
    have children := fun child code (receipt : CompatibleExpressionCalls.Entries scope _ scope child code) =>
      ih child code receipt.2
    cases head with
    | primitive head => exact primitive_native head children
    | constructor receipt _ _ sequence =>
      have packed := packed_native sequence children
      have registered := extension.constructor_lookup receipt.registered
      rw [← packed_type] at registered
      obtain ⟨_, ownerRegistered⟩ := DataEnvironment.lookupConstructorPayloadType?_owner registered
      exact ⟨.namedData ownerRegistered, SourceCoreCompatibleDataExpressions.construct_hasType _ registered packed.2⟩
    | member _ baseMetadata _ layout child =>
      have childType := child_type layout baseMetadata.projected
      exact ⟨(result_wellFormed layout).extend_definitions extension, layout_native_at extension layout shaped complete
        (by rw [← childType]; exact (children _ _ child).2)⟩
    | index header _ _ _ first second => exact index_native_at header (children _ _ first) (children _ _ second) (reasonAt _) extension
    | builtin head => exact BuiltinCallNativeTyping.Head.native head children
    | call head => exact callTyped head children
    | tuple _ sequence => exact packed_native sequence children

include shaped complete slots in
theorem tree_native_with (callerEvidence : Option Dynamic.EvidenceEnvironment)
    (tree : CompatibleExpressionCalls.Tree (RecursiveNamedCallEvidenceHeads.Calls callerEvidence headers compilation source context) readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  apply tree_native_for shaped complete (.refl _)
    (RecursiveNamedCallEvidenceHeads.Calls callerEvidence headers compilation source context) (tree := tree)
  intro children scope id lowered head typed
  cases callerEvidence with
  | none => exact named_native slots head typed
  | some evidence => exact RecursiveNamedCallEvidenceHeads.native slots head typed

include shaped complete slots in
theorem tree_native
    (tree : Expressions headers compilation readFuel source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered :=
  tree_native_with shaped complete slots none tree

include shaped complete slots in
theorem tree_native_at {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions)
    (tree : Expressions headers compilation readFuel source context solved reasonAt scope id lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  obtain ⟨wellFormed, typed⟩ := tree_native shaped complete slots tree
  exact ⟨wellFormed.extend_definitions extension, typed.extend_definitions extension⟩

include shaped complete slots in
/-- Expression support follows the same native derivation in the exact
source/global context. This does not prove support for an entire cached body,
whose parameter, allocator, loop and frame wrappers need separate inversion. -/
theorem tree_supported
    (tree : Expressions headers compilation readFuel source context solved reasonAt scope id lowered) :
    NativeExpressionContextSupport.supported lowered.expression (scope.length + administrative.length) = true := by
  simpa only [List.length_append, SourceCoreLocalCell.coreContext, List.length_map] using
    NativeExpressionContextSupport.of_typing (tree_native shaped complete slots tree).2

include shaped complete slots in
theorem tree_native_with_at (callerEvidence : Option Dynamic.EvidenceEnvironment) {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions)
    (tree : CompatibleExpressionCalls.Tree (RecursiveNamedCallEvidenceHeads.Calls callerEvidence headers compilation source context)
      readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  obtain ⟨wellFormed, typed⟩ := tree_native_with shaped complete slots callerEvidence tree
  exact ⟨wellFormed.extend_definitions extension, typed.extend_definitions extension⟩

include shaped complete slots in
theorem tree_supported_with (callerEvidence : Option Dynamic.EvidenceEnvironment)
    (tree : CompatibleExpressionCalls.Tree (RecursiveNamedCallEvidenceHeads.Calls callerEvidence headers compilation source context)
      readFuel values source context solved reasonAt scope id lowered) :
    NativeExpressionContextSupport.supported lowered.expression (scope.length + administrative.length) = true := by
  simpa only [List.length_append, SourceCoreLocalCell.coreContext, List.length_map] using
    NativeExpressionContextSupport.of_typing (tree_native_with shaped complete slots callerEvidence tree).2

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionNativeTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderContracts
/-! Measured stopping receipts for existing protected headers. The source
prefix and the original Core continuation have independent sizes. Empty
headers can retain the entire Core derivation, so continuation contracts use
an inclusive fixed bound; expression and body callbacks remain strictly below
that bound. The actual Tail and result receipts share one context predicate;
ordinary entry points specialize it without changing the static Tree. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory (NativeFrame)
open ProtectedForHeader (Tail TailFor Scope ValuesContext)

/-- A continuation may use the outer size itself when the prefix is empty. -/
def AtMost (budget : Nat) (contract : Nat → Prop) : Prop :=
  ∀ size, size ≤ budget → contract size

theorem AtMost.restrict {contract : Nat → Prop} {small large : Nat}
    (meaning : AtMost large contract) (bounded : small ≤ large) : AtMost small contract :=
  fun size smaller => meaning size (Nat.le_trans smaller bounded)

theorem AtMost.below {contract : Nat → Prop} {budget : Nat}
    (meaning : AtMost budget contract) : RecursiveNamedBoundedContracts.Below budget contract :=
  fun size smaller => meaning size (Nat.le_of_lt smaller)

def ContinuationWithin (budget : Nat)
    (meaning : Nat → SourceSemantics.Context → Scope → Expr → Prop)
    (context : SourceSemantics.Context) (scope : Scope) (code : Expr) : Prop :=
  AtMost budget (fun size => meaning size context scope code)

inductive ResultAtFor (validity : SourceSemantics.Context → Prop) (headerSize : Nat) {entry : ProtectedExpressionMeaning.Entry} {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (program : Program) (source : TypedSource) (solved : List SolvedRequirement) (evidence : Dynamic.EvidenceEnvironment)
    (administrative : Core.Context) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : NativeFrame) (type : Ty) (faults : FunctionCalls.FaultRep)
    (continuation : SourceSemantics.Context → Scope → Expr → Prop)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (items : List ForItemForm) (mapping : LocationMap) (world : StoreTyping) (store : Store)
    (value : Value) (finalStore : Store) : Prop where
  | continues {sourceSize remainingSize finalContext finalEnvironment after}
      (tail : TailFor validity (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after)
      (trace : SourceExecutionSize.ForItemsExecute program sourceSize context evidence source environment before items finalContext finalEnvironment after)
      (maps : LocationMap.Extends mapping tail.mapping) (worlds : WorldExtends world tail.world)
      (preservation : AdministrativePreserved mapping store tail.mapping tail.store)
      (metadata : Dynamic.HeapMetadataExtend before after)
      (remaining : EvaluationSize remainingSize tail.actual tail.store (tail.code.rename tail.embedding) value finalStore)
      (bounded : remainingSize ≤ headerSize) :
      ResultAtFor validity headerSize (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
        context environment before items mapping world store value finalStore
  | fault {sourceSize finalContext reason token after finalMap finalWorld}
      (trace : SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment before items finalContext reason after)
      (same : value = .inLeft (LocalLoop.controlType type) (.word token)) (matched : faults reason token)
      (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (preservation : AdministrativePreserved mapping store finalMap finalStore)
      (metadata : Dynamic.HeapMetadataExtend before after) :
      ResultAtFor validity headerSize (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
        context environment before items mapping world store value finalStore

abbrev ResultAt (headerSize : Nat) {entry : ProtectedExpressionMeaning.Entry} {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (program : Program) (source : TypedSource) (solved : List SolvedRequirement) (evidence : Dynamic.EvidenceEnvironment)
    (administrative : Core.Context) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : NativeFrame) (type : Ty) (faults : FunctionCalls.FaultRep)
    (continuation : SourceSemantics.Context → Scope → Expr → Prop)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (items : List ForItemForm) (mapping : LocationMap) (world : StoreTyping) (store : Store)
    (value : Value) (finalStore : Store) : Prop :=
  ResultAtFor (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) headerSize
    (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
    context environment before items mapping world store value finalStore

variable {entry : ProtectedExpressionMeaning.Entry} {values : GenericForHeader.ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {functions : FunctionModel values.checked.catalog ambient} {program : Program} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {solved : List SolvedRequirement} {administrative : Core.Context}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {registry : SourceCoreRawMetadata.Registry} {type : Ty} {faults : FunctionCalls.FaultRep}
  {continuation : SourceSemantics.Context → SourceCoreLocalCell.Scope → Expr → Prop}

/-- Forget bounds only in the safe direction. The source prefix, tail,
heap effects, and actual environment are retained field for field. -/
theorem ResultAtFor.erase {validity : SourceSemantics.Context → Prop} {headerSize : Nat} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before : Dynamic.Heap} {items : List ForItemForm}
    {mapping : LocationMap} {world : StoreTyping} {store finalStore : Store}
    {contextLocation : Location} {native : NativeFrame} {value : Value}
    (result : ResultAtFor validity headerSize (entry := entry) registry functions program source solved evidence
      administrative frame globals contextLocation native type faults continuation context environment before items
      mapping world store value finalStore) :
    ProtectedForHeader.ResultFor validity (entry := entry) registry functions program source solved evidence
      administrative frame globals contextLocation native type faults continuation context environment before items
      mapping world store value finalStore := by
  cases result with
  | continues tail trace maps worlds preservation metadata remaining _ =>
    exact .continues tail trace.sound maps worlds preservation metadata remaining.sound
  | fault trace same matched heaps maps worlds preservation metadata =>
    exact .fault trace.sound same matched heaps maps worlds preservation metadata

theorem ResultAt.erase {headerSize : Nat} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before : Dynamic.Heap} {items : List ForItemForm}
    {mapping : LocationMap} {world : StoreTyping} {store finalStore : Store}
    {contextLocation : Location} {native : NativeFrame} {value : Value}
    (result : ResultAt headerSize (entry := entry) registry functions program source solved evidence
      administrative frame globals contextLocation native type faults continuation context environment before items
      mapping world store value finalStore) :
    ProtectedForHeader.Result (entry := entry) registry functions program source solved evidence
      administrative frame globals contextLocation native type faults continuation context environment before items
      mapping world store value finalStore :=
  ResultAtFor.erase result

theorem ResultAtFor.prepend {validity : SourceSemantics.Context → Prop} {headerSize childSize headSize : Nat} {context middleContext : SourceSemantics.Context}
    {environment nextEnvironment : Dynamic.Environment} {before middle : Dynamic.Heap}
    {item : ForItemForm} {items : List ForItemForm}
    {mapping nextMap : LocationMap} {world nextWorld : StoreTyping} {store middleStore finalStore : Store}
    {contextLocation : Location} {native : NativeFrame} {value : Value}
    (head : SourceExecutionSize.ForItemExecutes program headSize context evidence source environment before item middleContext nextEnvironment middle)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld)
    (preservation : AdministrativePreserved mapping store nextMap middleStore)
    (metadata : Dynamic.HeapMetadataExtend before middle)
    (bounded : childSize ≤ headerSize)
    (tail : ResultAtFor validity childSize (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      middleContext nextEnvironment middle items nextMap nextWorld middleStore value finalStore) :
    ResultAtFor validity headerSize (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before (item :: items) mapping world store value finalStore := by
  cases tail with
  | continues tail trace lastMaps lastWorlds lastFrame lastMetadata remaining remainingBound =>
    exact .continues tail (.cons head trace) (maps.trans lastMaps) (worlds.trans lastWorlds)
      (preservation.trans lastFrame) (metadata.trans lastMetadata) remaining (Nat.le_trans remainingBound bounded)
  | fault trace same matched heaps lastMaps lastWorlds lastFrame lastMetadata =>
    exact .fault (.tail head trace) same matched heaps (maps.trans lastMaps) (worlds.trans lastWorlds)
      (preservation.trans lastFrame) (metadata.trans lastMetadata)

theorem ResultAt.prepend {headerSize childSize headSize : Nat} {context middleContext : SourceSemantics.Context}
    {environment nextEnvironment : Dynamic.Environment} {before middle : Dynamic.Heap}
    {item : ForItemForm} {items : List ForItemForm}
    {mapping nextMap : LocationMap} {world nextWorld : StoreTyping} {store middleStore finalStore : Store}
    {contextLocation : Location} {native : NativeFrame} {value : Value}
    (head : SourceExecutionSize.ForItemExecutes program headSize context evidence source environment before item middleContext nextEnvironment middle)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld)
    (preservation : AdministrativePreserved mapping store nextMap middleStore)
    (metadata : Dynamic.HeapMetadataExtend before middle)
    (bounded : childSize ≤ headerSize)
    (tail : ResultAt childSize (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      middleContext nextEnvironment middle items nextMap nextWorld middleStore value finalStore) :
    ResultAt headerSize (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before (item :: items) mapping world store value finalStore :=
  ResultAtFor.prepend head maps worlds preservation metadata bounded tail

/-- The empty prefix retains the original derivation, including equal size. -/
theorem ResultAtFor.nil {validity : SourceSemantics.Context → Prop} {size : Nat} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {contextLocation : Location} {native : NativeFrame} {value : Value} {finalStore : Store}
    (tail : TailFor validity (entry := entry) registry functions source solved evidence administrative frame globals
      contextLocation native continuation context environment heap)
    (evaluated : EvaluationSize size tail.actual tail.store (tail.code.rename tail.embedding) value finalStore) :
    ResultAtFor validity size (entry := entry) registry functions program source solved evidence administrative frame globals
      contextLocation native type faults continuation context environment heap [] tail.mapping tail.world tail.store value finalStore :=
  .continues tail .nil (.refl _) (.refl _) (.refl _ _) (.refl _) evaluated (Nat.le_refl _)

theorem ResultAt.nil {size : Nat} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {contextLocation : Location} {native : NativeFrame} {value : Value} {finalStore : Store}
    (tail : Tail (entry := entry) registry functions source solved evidence administrative frame globals
      contextLocation native continuation context environment heap)
    (evaluated : EvaluationSize size tail.actual tail.store (tail.code.rename tail.embedding) value finalStore) :
    ResultAt size (entry := entry) registry functions program source solved evidence administrative frame globals
      contextLocation native type faults continuation context environment heap [] tail.mapping tail.world tail.store value finalStore :=
  ResultAtFor.nil tail evaluated

/-- Instantiate an inclusive continuation with the actual remaining size. -/
theorem tail_at_remaining_for {validity : SourceSemantics.Context → Prop} {budget headerSize remainingSize : Nat}
    {meaning : Nat → SourceSemantics.Context → Scope → Expr → Prop}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {contextLocation : Location} {native : NativeFrame}
    (tail : TailFor validity (entry := entry) registry functions source solved evidence administrative frame globals
      contextLocation native (ContinuationWithin budget meaning) context environment heap)
    (remainingBound : remainingSize ≤ headerSize) (headerBound : headerSize ≤ budget) :
    meaning remainingSize context tail.scope tail.code :=
  tail.certificate remainingSize (Nat.le_trans remainingBound headerBound)

theorem tail_at_remaining {budget headerSize remainingSize : Nat}
    {meaning : Nat → SourceSemantics.Context → Scope → Expr → Prop}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {contextLocation : Location} {native : NativeFrame}
    (tail : Tail (entry := entry) registry functions source solved evidence administrative frame globals
      contextLocation native (ContinuationWithin budget meaning) context environment heap)
    (remainingBound : remainingSize ≤ headerSize) (headerBound : headerSize ≤ budget) :
    meaning remainingSize context tail.scope tail.code :=
  tail_at_remaining_for tail remainingBound headerBound

/-- Retain the two actual source children, including the reached lexical scope. -/
theorem source_cons_children {program : Program} {size : Nat}
    {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment finalEnvironment : Dynamic.Environment}
    {before after : Dynamic.Heap} {item : ForItemForm} {items : List ForItemForm}
    (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before
      (item :: items) finalContext finalEnvironment after) :
    ∃ headSize tailSize middleContext nextEnvironment middle,
      SourceExecutionSize.ForItemExecutes program headSize context evidence source environment before
        item middleContext nextEnvironment middle ∧
      SourceExecutionSize.ForItemsExecute program tailSize middleContext evidence source nextEnvironment middle
        items finalContext finalEnvironment after ∧
      headSize < size ∧ tailSize < size := by
  cases trace with
  | cons head tail =>
    exact ⟨_, _, _, _, _, head, tail,
      SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp)⟩

/-- A first-item fault keeps the entry context. A later fault retains the
successful source prefix and its actual intermediate environment and heap. -/
theorem source_fault_children {program : Program} {size : Nat}
    {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {item : ForItemForm} {items : List ForItemForm}
    {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before
      (item :: items) finalContext reason after) :
    (finalContext = context ∧ ∃ childSize,
      SourceExecutionSize.ForItemFaults program childSize context evidence source environment before item reason after ∧
      childSize < size) ∨
    (∃ headSize tailSize middleContext nextEnvironment middle,
      SourceExecutionSize.ForItemExecutes program headSize context evidence source environment before
        item middleContext nextEnvironment middle ∧
      SourceExecutionSize.ForItemsFault program tailSize middleContext evidence source nextEnvironment middle
        items finalContext reason after ∧
      headSize < size ∧ tailSize < size) := by
  cases trace with
  | head failed =>
    exact .inl ⟨rfl, _, failed, SourceExecutionSize.child_lt_stepSize (by simp)⟩
  | tail head failed =>
    exact .inr ⟨_, _, _, _, _, head, failed,
      SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp)⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedBuiltinCallBounds
/-! The real builtin call exposes ordered arguments below its original
source or native execution size. Callee construction and contract dispatch
are pure prefixes; their semantic agreement supplies no size bound. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedBuiltinCallBounds
open Core Frontend SourceInference CoreProof CompatibleExpressionPrimitives
open BuiltinCalls BuiltinCalls.Protocol RecursiveNamedCallBounds

inductive SourceTraceAt (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (arguments : List ExpressionId) (function : BuiltinFunctionId) (size : Nat) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | argumentsFault {child reason after}
      (failed : SourceExecutionSize.ExpressionsFault program child context evidence source environment before arguments reason after)
      (smaller : child < size) :
      SourceTraceAt program context evidence source environment before arguments function size (.fault reason) after
  | apply {child values middle outcome after}
      (argumentsEvaluated : SourceExecutionSize.ExpressionsEvaluate program child context evidence source environment before arguments values middle)
      (applied : FunctionCallBody.Outcome program context evidence [] middle (.builtin ⟨function⟩) values outcome after)
      (smaller : child < size) :
      SourceTraceAt program context evidence source environment before arguments function size outcome after

theorem source_inv {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id callee : ExpressionId}
    {node : ExpressionNode} {type : Ty} {arguments : List ExpressionId} {function : BuiltinFunctionId}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome} {size : Nat}
    (metadata : Metadata checked source id node type)
    (form : node.form = .call callee arguments (.builtinFunction function)) (unique : NodeOccurrencesUnique source)
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) :
    SourceTraceAt program context evidence source environment before arguments function size outcome after := by
  cases trace with
  | value evaluated =>
    obtain ⟨child, raw, smaller⟩ := RecursiveNamedExpressionSourceBounds.evaluation_raw_sized unique
      (lookupExpression?_sound metadata.found) (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | builtinCall _ argumentsEvaluated applied =>
      exact .apply argumentsEvaluated (.value applied.sound)
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
  | fault failed =>
    obtain ⟨child, raw, smaller⟩ := RecursiveNamedExpressionSourceBounds.fault_raw_sized unique
      (lookupExpression?_sound metadata.found) (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | builtinArguments _ argumentsFailed =>
      exact .argumentsFault argumentsFailed
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
    | builtinApply _ argumentsEvaluated failed =>
      exact .apply argumentsEvaluated (.fault failed.sound)
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)

theorem contracted_arguments_sized {function : BuiltinFunctionId} {identity contract unknown : Word}
    {environment : Environment} {store finalStore : Store} {arguments : Expr} {result : Value} {size : Nat}
    (completed : EvaluationSize size environment store
      (CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
        (contracted function identity contract) arguments) result finalStore) :
    ∃ child argumentValue argumentStore, child < size ∧
      EvaluationSize child (.unit :: contractedValue function identity contract environment :: environment) store
        ((arguments.weakenAt 0).weakenAt 0) argumentValue argumentStore := by
  obtain ⟨tailSize, tailSmaller, tail⟩ := completed.bind_success
    (contracted_evaluates function identity contract environment store)
  have stage := CallableContract.dispatch_evaluates [⟨contract, none, none⟩] .beforeArguments unknown contract
    (show Evaluates (contractedValue function identity contract environment :: environment) store
      (.second (.var 0)) (.word contract) store from .second (.var rfl))
  rw [gates_accept] at stage
  obtain ⟨nextSize, nextSmaller, next⟩ := tail.bind_success stage
  obtain ⟨child, argumentStore, argumentValue, smaller, evaluated⟩ := next.bind_computation
  exact ⟨child, argumentValue, argumentStore, Nat.lt_trans smaller (Nat.lt_trans nextSmaller tailSmaller), evaluated⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedBuiltinCallBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedBuiltinHeadBounds
/-! The existing contracted builtin Head composes only finite argument
obligations within the fixed outer bound. It does not close the full recursive
expression Tree; source and native sizes remain independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedBuiltinHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload DataPatternValues CoreProof
open BuiltinCalls BuiltinCalls.Protocol
open BuiltinCalls.Typed (Head)
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CompatibleExpressionPrimitives (Metadata)
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope
private theorem values_rep {values : ValuesContext} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {types : List TypeSystem.Ty} {natives : List Ty}
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world types natives sources payloads) :
    ValuesRep values.checked registry functions mapping world types sources payloads natives := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

private theorem contracted_typed {definitions : DataEnvironment} {world : StoreTyping}
    {environment : Environment} {actualContext : Core.Context}
    (typed : RuntimeEnvironmentHasTypes world environment actualContext definitions)
    (function : BuiltinFunctionId) (identity contract : Word) :
    RuntimeValueHasType world (contractedValue function identity contract environment)
      (CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function))
      definitions := by
  have closureTyped := SourceCoreInteger.builtinClosure_hasType (scope := actualContext) (definitions := definitions) function
  cases closureTyped with
  | lambda _ _ body => exact .pair (.pair (.inRight .word) (.closure typed body)) .word

private theorem contracted_rename (function : BuiltinFunctionId) (identity contract : Word) (ξ : Renaming) :
    (Protocol.contracted function identity contract).rename ξ = Protocol.contracted function identity contract := by
  cases function <;> rfl

private theorem call_rename (function : BuiltinFunctionId) (identity contract unknown : Word)
    (arguments : Expr) (ξ : Renaming) :
    (CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
      (Protocol.contracted function identity contract) arguments).rename ξ =
    CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
      (Protocol.contracted function identity contract) (arguments.rename ξ) := by
  simp [CallableContract.call, LanguageResult.bind, CallableContract.dispatch, CallableContract.guardResult,
    CallableContract.Gate.reason, LanguageResult.success, LanguageResult.failure,
    contracted_rename, Expr.rename, Renaming.lift]


variable {fuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

variable {certificate : GenericExpressionMeaning.Certificate}
namespace Stateful
universe u v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)

/-- The guarded environment retains its original runtime typing. -/
theorem prefixed_typed {definitions : DataEnvironment} {world : StoreTyping}
    {actual : Environment} {actualContext : Core.Context}
    (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (function : BuiltinFunctionId) (identity contract : Word) :
    RuntimeEnvironmentHasTypes world (.unit :: contractedValue function identity contract actual :: actual)
      (.unit :: CallableContract.functionType (SourceCoreInteger.builtinParameter function)
        (SourceCoreInteger.builtinResult function) :: actualContext) definitions :=
  .cons .unit (.cons (contracted_typed typed function identity contract) typed)

include functionLeaves unique in
/-- The original Source head consumes a whole sequence at the real guarded
caller input. Builtin application keeps that exact argument post. -/
theorem Head.preserves_bounded_with_sequence (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
    {function : BuiltinFunctionId} {node : ExpressionNode} {codes : List SourceCoreBasic.LoweredExpr}
    {identity contract unknown : Word}
    (metadata : Metadata values.checked source id node (SourceCoreInteger.builtinResult function))
    (form : node.form = .call callee arguments (.builtinFunction function))
    (sourceType : node.type = function.returnType)
    (nativeTypes : codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequence : ProtectedStateExpressionSequenceProducer.Preserves
      (program := program) (context := context) (evidence := evidence) (source := source)
      (environment := environment) (actual := .unit :: contractedValue function identity contract actual :: actual)
      (ξ := Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      (ids := arguments) (sourceTypes := function.parameterTypes) (codes := codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) initial (budget + 1))
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
        (Protocol.contracted function identity contract) (SourceCoreCalls.packArguments codes).expression).rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld node.type
        (SourceCoreInteger.builtinResult function) faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have sourceTrace := RecursiveNamedBuiltinCallBounds.source_inv metadata form unique trace
  cases sourceTrace with
  | argumentsFault failed smaller =>
    obtain ⟨argumentValue, finalStore, finalMap, finalWorld, argumentEval, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
      sequence (.fault failed) (by omega)
    cases represented with
    | @fault reason token matched =>
      rw [rename_prefix, rename_prefix] at argumentEval
      refine ⟨.inLeft _ (.word token), finalStore, finalMap, finalWorld, ?_, .fault matched,
        finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
      rw [call_rename]
      exact CallableContract.call_argument_failure [⟨contract, none, none⟩] unknown
        (contracted_evaluates function identity contract actual store) (gates_accept contract unknown .beforeArguments) argumentEval
  | apply argumentsEvaluated application smaller =>
    obtain ⟨argumentValue, argumentStore, finalMap, finalWorld, argumentEval, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
      sequence (.values argumentsEvaluated) (by omega)
    cases represented with
    | values represented =>
      have related := values_rep represented
      rw [nativeTypes] at related
      have inputs := CompatibleBuiltinMeaning.input_of_values functionLeaves related
      rw [rename_prefix, rename_prefix] at argumentEval
      cases application with
      | value applied =>
        cases applied with
        | builtin applied =>
          obtain ⟨sourceResult, nativeResult, appliedAgain, resultRep, completed⟩ := contracted_preserves inputs argumentEval
          have same := appliedAgain.functional applied
          subst sourceResult
          refine ⟨.inRight .word nativeResult, argumentStore, finalMap, finalWorld, ?_, ?_,
            finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
          · rw [call_rename]; exact completed
          · rw [sourceType]; exact .value (CompatibleBuiltinMeaning.result_represents inputs applied resultRep)
      | fault failed => exact False.elim (InputRep.excludes_callable_fault inputs failed)


include functionLeaves in
/-- The original reflection suffix uses the actual measured argument child
and retains its real post with an independent Source grade. -/
theorem Head.reflects_after_arguments_with_sequence (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
    {function : BuiltinFunctionId} {node : ExpressionNode} {codes : List SourceCoreBasic.LoweredExpr}
    {identity contract unknown : Word}
    (metadata : Metadata values.checked source id node (SourceCoreInteger.builtinResult function))
    (form : node.form = .call callee arguments (.builtinFunction function))
    (sourceType : node.type = function.returnType)
    (nativeTypes : codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequence : ProtectedStateExpressionSequenceProducer.Reflects
      (program := program) (context := context) (evidence := evidence) (source := source)
      (environment := environment) (actual := .unit :: contractedValue function identity contract actual :: actual)
      (ξ := Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      (ids := arguments) (sourceTypes := function.parameterTypes) (codes := codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) initial (budget + 1))
    {result : Value} {finalStore : Store} (argumentSize : Nat)
    {argumentValue : Value} {argumentStore : Store}
    (argumentSmaller : argumentSize < size)
    (argumentEval : EvaluationSize argumentSize (.unit :: contractedValue function identity contract actual :: actual) store
      (((SourceCoreCalls.packArguments codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0) argumentValue argumentStore)
    (completed : EvaluationSize size actual store (CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
        (Protocol.contracted function identity contract) ((SourceCoreCalls.packArguments codes).expression.rename ξ)) result finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld node.type
        (SourceCoreInteger.builtinResult function) faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have shifted := argumentEval
  rw [← rename_prefix, ← rename_prefix] at shifted
  obtain ⟨argumentSourceSize, argumentOutcome, middle, finalMap, finalWorld, argumentTrace, represented, finalHeaps,
    maps, worlds, frame, heapMetadata, transition⟩ :=
    sequence shifted (by omega)
  cases represented with
  | values represented =>
    cases argumentTrace with
    | values sourceArgs =>
      have related := values_rep represented
      rw [nativeTypes] at related
      have inputs := CompatibleBuiltinMeaning.input_of_values functionLeaves related
      obtain ⟨sourceResult, nativeResult, applied, resultRep, resultEq, storesEq⟩ := contracted_reflects inputs argumentEval.sound completed.sound
      subst result
      subst finalStore
      obtain ⟨sourceSize, sourceTrace⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
        (BuiltinCalls.source_intro metadata form (.apply sourceArgs.sound (.value (.builtin applied))))
      refine ⟨sourceSize, .value sourceResult, middle, finalMap, finalWorld, sourceTrace, ?_,
        finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
      rw [sourceType]; exact .value (CompatibleBuiltinMeaning.result_represents inputs applied resultRep)
  | fault matched =>
    cases argumentTrace with
    | fault sourceArgs =>
      have failed := CallableContract.call_argument_failure (result := SourceCoreInteger.builtinResult function)
        [⟨contract, none, none⟩] unknown (contracted_evaluates function identity contract actual store)
        (gates_accept contract unknown .beforeArguments) argumentEval.sound
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound failed
      obtain ⟨sourceSize, sourceTrace⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
        (BuiltinCalls.source_intro metadata form (.argumentsFault sourceArgs.sound))
      exact ⟨sourceSize, .fault _, middle, finalMap, finalWorld, sourceTrace,
        .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩

include functionLeaves in
/-- Invert the same original contracted call once before consuming its real
argument child through the shared reflection suffix. -/
theorem Head.reflects_bounded_with_sequence (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
    {function : BuiltinFunctionId} {node : ExpressionNode} {codes : List SourceCoreBasic.LoweredExpr}
    {identity contract unknown : Word}
    (metadata : Metadata values.checked source id node (SourceCoreInteger.builtinResult function))
    (form : node.form = .call callee arguments (.builtinFunction function))
    (sourceType : node.type = function.returnType)
    (nativeTypes : codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequence : ProtectedStateExpressionSequenceProducer.Reflects
      (program := program) (context := context) (evidence := evidence) (source := source)
      (environment := environment) (actual := .unit :: contractedValue function identity contract actual :: actual)
      (ξ := Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      (ids := arguments) (sourceTypes := function.parameterTypes) (codes := codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) initial (budget + 1))
    {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store ((CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
        (Protocol.contracted function identity contract) (SourceCoreCalls.packArguments codes).expression).rename ξ) result finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld node.type
        (SourceCoreInteger.builtinResult function) faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  rw [call_rename] at completed
  obtain ⟨argumentSize, argumentValue, argumentStore, argumentSmaller, argumentEval⟩ :=
    RecursiveNamedBuiltinCallBounds.contracted_arguments_sized completed
  exact Head.reflects_after_arguments_with_sequence functions functionLeaves program evidence protocol budget size bounded
    metadata form sourceType nativeTypes initial sequence argumentSize argumentSmaller argumentEval completed

include functionLeaves unique in
theorem Head.preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (argumentMeaning : ∀ child, child ≤ budget → ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults child) :
    ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head values source certificate) faults size := by
  intro scope id lowered tree
  cases tree with
  | @contracted callee arguments function node codes identity contract unknown metadata form sourceType children nativeTypes =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have prefixedLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
        canonical (.unit :: contractedValue function identity contract actual :: actual) := agree_prefix (agree_prefix agrees (contractedValue function identity contract actual)) .unit
    have prefixedTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (definitions := ambient.definitions))
      (.cons (contracted_typed actualTyped function identity contract) actualTyped)
    exact Head.preserves_bounded_with_sequence functions functionLeaves program evidence unique protocol budget size bounded
      metadata form sourceType nativeTypes installedEntry
      (ProtectedStateExpressionSequenceProducer.Preserves.of_uniform installedEntry (budget + 1) children
        (fun child within => ProtectedStateTransition.SequenceBridge.preserves_at protocol (argumentMeaning child (by omega)))
        environments heaps locals prefixedLayout prefixedTyped) trace

include functionLeaves in
theorem Head.reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (argumentMeaning : ∀ child, child ≤ budget → ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults child) :
    ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head values source certificate) faults size := by
  intro scope id lowered tree
  cases tree with
  | @contracted callee arguments function node codes identity contract unknown metadata form sourceType children nativeTypes =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ result finalStore
      environments heaps locals agrees actualTyped installedEntry completed
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [call_rename] at completed
    obtain ⟨argumentSize, argumentValue, argumentStore, argumentSmaller, argumentEval⟩ :=
      RecursiveNamedBuiltinCallBounds.contracted_arguments_sized completed
    have prefixedLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
        canonical (.unit :: contractedValue function identity contract actual :: actual) := agree_prefix (agree_prefix agrees (contractedValue function identity contract actual)) .unit
    have prefixedTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (definitions := ambient.definitions))
      (.cons (contracted_typed actualTyped function identity contract) actualTyped)
    exact Head.reflects_after_arguments_with_sequence functions functionLeaves program evidence protocol budget size bounded
      metadata form sourceType nativeTypes installedEntry
      (ProtectedStateExpressionSequenceProducer.Reflects.of_uniform installedEntry (budget + 1) children
        (fun child within => ProtectedStateTransition.SequenceBridge.reflects_at protocol (argumentMeaning child (by omega)))
        environments heaps locals prefixedLayout prefixedTyped) argumentSize argumentSmaller argumentEval completed

end Stateful

variable {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
include transport

include functionLeaves unique in
theorem Head.preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (argumentMeaning : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head values source certificate) faults entry := by
  intro scope id lowered tree node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped installedEntry trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.Head.preserves_at functions functionLeaves program evidence unique (ProtectedStatePlaceAssignment.legacyProtocol entry) budget size bounded
      (fun child bound => ProtectedStatePlaceAssignment.legacy_preserves transport (argumentMeaning child bound))
      tree found environments heaps locals agrees actualTyped (PLift.up installedEntry) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

include functionLeaves in
theorem Head.reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (argumentMeaning : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head values source certificate) faults entry := by
  intro scope id lowered tree node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped installedEntry evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.Head.reflects_at functions functionLeaves program evidence (ProtectedStatePlaceAssignment.legacyProtocol entry) budget size bounded
      (fun child bound => ProtectedStatePlaceAssignment.legacy_reflects transport (argumentMeaning child bound))
      tree found environments heaps locals agrees actualTyped (PLift.up installedEntry) evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedBuiltinHeadBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionTreeBounds
/-! The existing recursive expression Tree closes its child obligations within
one inclusive budget. All catalog body obligations remain explicit below that
budget for the subsequent mutual induction. Static syntax and receipts do not
contain body execution. Source and native costs are independent. The
authenticated family fixes the same caller evidence for every child; only its
source call inversion additionally consumes requirement ID uniqueness. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds

universe u v

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix : Nat} {compilation : SourceCoreFunctions.Context}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  {literals : GenericExpressionMeaning.Certificate}
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {certificate : GenericExpressionMeaning.Certificate}

private def pointCertificate (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current expression code => current = scope ∧ expression = id ∧ code = lowered

/-- One support fold serves every pointwise meaning family. Child membership
retains the original ordered Entries certificate and the same inclusive budget. -/
theorem fold_at_with_literals
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (Meaning : Nat → SourceCoreLocalCell.Scope → ExpressionId → SourceCoreBasic.LoweredExpr → Prop)
    (budget : Nat)
    (fragments : ∀ size, size ≤ budget → ∀ {scope id lowered}
      (child : CompatibleExpressionBuiltins.Tree fuel values source context solved reasonAt scope id lowered),
      child.LiteralSites literals → Meaning size scope id lowered)
    (heads : ∀ certificate size, size ≤ budget →
      (∀ child, child ≤ budget → ∀ {scope id lowered}, certificate scope id lowered → Meaning child scope id lowered) →
      ∀ {scope id lowered}, CompatibleExpressionCalls.Head calls values source context reasonAt certificate scope id lowered →
        Meaning size scope id lowered)
    {size : Nat} (within : size ≤ budget) {scope id lowered}
    (tree : CompatibleExpressionCalls.Tree calls fuel values source context solved reasonAt scope id lowered)
    (sites : tree.LiteralSites literals) : Meaning size scope id lowered := by
  induction sites generalizing size with
  | fragment child childSites => exact fragments size within child childSites
  | @node id lowered entries head children childSites ih =>
    have meanings : ∀ child, child ≤ budget → ∀ {current expression code},
        CompatibleExpressionCalls.Entries scope entries current expression code → Meaning child current expression code := by
      intro child childWithin current expression code certified
      obtain ⟨rfl, member⟩ := certified
      exact ih expression code member childWithin
    exact heads _ size within meanings head

/-- Certificate selection and gathering adapt the same support fold to a
bounded contract. These operations change only its static certificate premise. -/
theorem fold_contract_at_with_literals
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (Meaning : Nat → GenericExpressionMeaning.Certificate → Prop)
    (select : ∀ {size certificate}, Meaning size certificate → ∀ {scope id lowered},
      certificate scope id lowered → Meaning size (pointCertificate scope id lowered))
    (gather : ∀ {size certificate},
      (∀ {scope id lowered}, certificate scope id lowered → Meaning size (pointCertificate scope id lowered)) →
      Meaning size certificate)
    (budget size : Nat) (within : size ≤ budget)
    (fragments : ∀ child, child ≤ budget → Meaning child
      (CompatibleExpressionBuiltins.Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals))
    (heads : ∀ certificate child, child ≤ budget →
      (∀ smaller, smaller ≤ budget → Meaning smaller certificate) →
      Meaning child (CompatibleExpressionCalls.Head calls values source context reasonAt certificate)) :
    Meaning size (CompatibleExpressionCalls.Tree.WithLiterals (calls := calls)
      (fuel := fuel) (values := values) (source := source) (context := context) (solved := solved)
      (reasonAt := reasonAt) literals) := by
  apply gather
  intro scope id lowered supported
  obtain ⟨tree, sites⟩ := supported
  exact fold_at_with_literals calls (fun child scope id lowered => Meaning child (pointCertificate scope id lowered))
    budget (fun child childWithin _ _ _ fragment sites => select (fragments child childWithin) ⟨fragment, sites⟩)
    (fun certificate child childWithin children _ _ _ head =>
      select (heads certificate child childWithin (fun smaller smallerWithin => gather (children smaller smallerWithin))) head)
    within tree sites

/-- Stateful fragments and heads return their actual post-witnesses. The same
support fold supplies each ordered child at the original inclusive budget. -/
theorem preserves_at_with_state {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (budget size : Nat) (within : size ≤ budget)
    (fragments : ∀ child, child ≤ budget → ProtectedStateTransition.PreservesAt protocol
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
      (CompatibleExpressionBuiltins.Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults child)
    (heads : ∀ certificate child, child ≤ budget →
      (∀ smaller, smaller ≤ budget → ProtectedStateTransition.PreservesAt protocol
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults smaller) →
      ProtectedStateTransition.PreservesAt protocol
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
        (CompatibleExpressionCalls.Head calls values source context reasonAt certificate) faults child) :
    ProtectedStateTransition.PreservesAt protocol
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := calls) (fuel := fuel) (values := values)
        (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  exact fold_contract_at_with_literals calls
    (fun child certificate => ProtectedStateTransition.PreservesAt protocol
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults child)
    (fun meaning _ _ _ certified _ _ _ point => by
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact meaning certified)
    (fun meanings scope id lowered certified => meanings certified ⟨rfl, rfl, rfl⟩)
    budget size within fragments heads

/-- Original Core grades choose the stateful child contracts; Source grades
and the concrete reached witnesses are returned by those same contracts. -/
theorem reflects_at_with_state {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (budget size : Nat) (within : size ≤ budget)
    (fragments : ∀ child, child ≤ budget → ProtectedStateTransition.ReflectsAt protocol
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
      (CompatibleExpressionBuiltins.Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults child)
    (heads : ∀ certificate child, child ≤ budget →
      (∀ smaller, smaller ≤ budget → ProtectedStateTransition.ReflectsAt protocol
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults smaller) →
      ProtectedStateTransition.ReflectsAt protocol
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
        (CompatibleExpressionCalls.Head calls values source context reasonAt certificate) faults child) :
    ProtectedStateTransition.ReflectsAt protocol
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := calls) (fuel := fuel) (values := values)
        (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  exact fold_contract_at_with_literals calls
    (fun child certificate => ProtectedStateTransition.ReflectsAt protocol
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults child)
    (fun meaning _ _ _ certified _ _ _ point => by
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact meaning certified)
    (fun meanings scope id lowered certified => meanings certified ⟨rfl, rfl, rfl⟩)
    budget size within fragments heads

include extension faithful functionLeaves functionTypes unique missing in
/-- Every existing head uses child obligations at the same inclusive budget;
only an actual named callee consumes the strictly smaller body contract. -/
theorem head_preserves_at_with_calls [FunctionCalls.FaultTokens faults] (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P)
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.PreservesAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      P)
    (callMeaning : RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
      (calls certificate) faults P) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head (calls)
        values source context reasonAt certificate) faults
      P := by
  intro scope id lowered head
  cases head with
  | primitive head =>
    exact RecursiveNamedExpressionCompositionsBounds.Head.preserves_at functions program evidence
      transport budget size within unique children head
  | constructor receipt form accepted sequence =>
    exact RecursiveNamedDataExpressionHeadBounds.preserves_at (calls := calls) functions extension faithful functionLeaves functionTypes
      program evidence unique missing transport budget size within children
      ⟨.constructor receipt form accepted sequence, .constructor receipt form accepted sequence⟩
  | member metadata baseMetadata form layout certified =>
    exact RecursiveNamedDataExpressionHeadBounds.preserves_at (calls := calls) functions extension faithful functionLeaves functionTypes
      program evidence unique missing transport budget size within children
      ⟨.member metadata baseMetadata form layout certified, .member metadata baseMetadata form layout certified⟩
  | index header found form sourceType first second =>
    exact RecursiveNamedDataExpressionHeadBounds.preserves_at (calls := calls) functions extension faithful functionLeaves functionTypes
      program evidence unique missing transport budget size within children
      ⟨.index header found form sourceType first second, .index header found form sourceType first second⟩
  | builtin head =>
    exact RecursiveNamedBuiltinHeadBounds.Head.preserves_at functions functionLeaves program evidence unique
      transport budget size within children head
  | tuple receipt sequence =>
    exact RecursiveNamedTupleHeadBounds.preserves_at functions program evidence transport budget size within unique children
      ⟨_, _, _, _, rfl, receipt, sequence⟩
  | call head => exact callMeaning head

include extension faithful functionLeaves functionTypes unique owners missing in
/-- Every existing head uses child obligations at the same inclusive budget;
only an actual named callee consumes the strictly smaller body contract. -/
theorem head_preserves_at_with_for [FunctionCalls.FaultTokens faults] (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P)
    (catalog : ∀ {scope mapping world heap store canonical}, P scope mapping world heap store canonical →
      protectedEntry headers locations capturePrefix compilation.administrativePrefix scope mapping world heap store canonical)
    (conditions : ∀ header, BodyCondition (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header)
    (authorized : ∀ header, header ∈ headers → BodyAuthorization (headers := headers) (locations := locations)
      (capturePrefix := capturePrefix) functions registry header (conditions header))
    (authenticated : Bool)
    (idsUnique : authenticated = true → RequirementIdsUnique context)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.PreservesAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      P)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (conditions header))) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head (RecursiveNamedCallEvidenceHeads.Calls (if authenticated then some evidence else none) headers compilation source context)
        values source context reasonAt certificate) faults
      P :=
  head_preserves_at_with_calls functions extension faithful functionLeaves functionTypes evidence unique missing P transport
    (RecursiveNamedCallEvidenceHeads.Calls (if authenticated then some evidence else none) headers compilation source context) budget size within children
    (by
      intro scope id lowered head
      cases authenticated with
      | false =>
        exact RecursiveNamedExpressionHeadBounds.preserves_at_for functions P transport catalog conditions authorized budget size within unique owners
          (fun child smaller => children child (Nat.le_of_lt smaller)) bodies head
      | true =>
        exact RecursiveNamedCallEvidenceHeads.preserves_at_for functions P transport catalog conditions authorized budget size within (idsUnique rfl) unique owners
          (fun child smaller => children child (Nat.le_of_lt smaller)) bodies head)

include extension faithful functionLeaves functionTypes unique owners missing in
theorem head_preserves_at_with [FunctionCalls.FaultTokens faults] (authenticated : Bool)
    (idsUnique : authenticated = true → RequirementIdsUnique context)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.PreservesAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix))
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head (RecursiveNamedCallEvidenceHeads.Calls (if authenticated then some evidence else none) headers compilation source context)
        values source context reasonAt certificate) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  head_preserves_at_with_for functions extension faithful functionLeaves functionTypes evidence unique owners missing
    _ entry_transport (fun entry => entry) (fun _ => fun {_ _ _ _ _ _ _ _ _ _ _ _} _ => True)
    (fun _ _ => by unfold BodyAuthorization; intros; trivial) authenticated idsUnique budget size within children
    (by
      intro header member child smaller arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry result after _ trace
      exact bodies header member child smaller entry trace)

include extension faithful functionLeaves functionTypes unique owners missing in
/-- Every existing head uses child obligations at the same inclusive budget;
only an actual named callee consumes the strictly smaller body contract. -/
theorem head_preserves_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.PreservesAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix))
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head (RecursiveNamedCatalog.Head headers compilation source context)
        values source context reasonAt certificate) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  head_preserves_at_with functions extension faithful functionLeaves functionTypes evidence unique owners missing false (fun impossible => Bool.noConfusion impossible) budget size within children bodies

include extension faithful functionLeaves functionTypes missing in
/-- Original native children select their own pointwise obligations. Reflection
constructs a separately measured source trace. -/
theorem head_reflects_at_with_calls [FunctionCalls.FaultTokens faults] (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P)
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.ReflectsAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      P)
    (callMeaning : RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
      (calls certificate) faults P) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head (calls)
        values source context reasonAt certificate) faults
      P := by
  intro scope id lowered head
  cases head with
  | primitive head =>
    exact RecursiveNamedExpressionCompositionsBounds.Head.reflects_at functions program evidence
      transport budget size within children head
  | constructor receipt form accepted sequence =>
    exact RecursiveNamedDataExpressionHeadBounds.reflects_at (calls := calls) functions extension faithful functionLeaves functionTypes
      program evidence missing transport budget size within children
      ⟨.constructor receipt form accepted sequence, .constructor receipt form accepted sequence⟩
  | member metadata baseMetadata form layout certified =>
    exact RecursiveNamedDataExpressionHeadBounds.reflects_at (calls := calls) functions extension faithful functionLeaves functionTypes
      program evidence missing transport budget size within children
      ⟨.member metadata baseMetadata form layout certified, .member metadata baseMetadata form layout certified⟩
  | index header found form sourceType first second =>
    exact RecursiveNamedDataExpressionHeadBounds.reflects_at (calls := calls) functions extension faithful functionLeaves functionTypes
      program evidence missing transport budget size within children
      ⟨.index header found form sourceType first second, .index header found form sourceType first second⟩
  | builtin head =>
    exact RecursiveNamedBuiltinHeadBounds.Head.reflects_at functions functionLeaves program evidence
      transport budget size within children head
  | tuple receipt sequence =>
    exact RecursiveNamedTupleHeadBounds.reflects_at functions program evidence transport budget size within children
      ⟨_, _, _, _, rfl, receipt, sequence⟩
  | call head => exact callMeaning head

include extension faithful functionLeaves functionTypes missing in
/-- Original native children select their own pointwise obligations. Reflection
constructs a separately measured source trace. -/
theorem head_reflects_at_with_for [FunctionCalls.FaultTokens faults] (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P)
    (catalog : ∀ {scope mapping world heap store canonical}, P scope mapping world heap store canonical →
      protectedEntry headers locations capturePrefix compilation.administrativePrefix scope mapping world heap store canonical)
    (conditions : ∀ header, BodyCondition (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header)
    (authorized : ∀ header, header ∈ headers → BodyAuthorization (headers := headers) (locations := locations)
      (capturePrefix := capturePrefix) functions registry header (conditions header))
    (authenticated : Bool)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.ReflectsAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      P)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (conditions header))) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head (RecursiveNamedCallEvidenceHeads.Calls (if authenticated then some evidence else none) headers compilation source context)
        values source context reasonAt certificate) faults
      P :=
  head_reflects_at_with_calls functions extension faithful functionLeaves functionTypes evidence missing P transport
    (RecursiveNamedCallEvidenceHeads.Calls (if authenticated then some evidence else none) headers compilation source context) budget size within children
    (by
      intro scope id lowered head
      cases authenticated with
      | false =>
        exact RecursiveNamedExpressionHeadBounds.reflects_at_for functions P transport catalog conditions authorized budget size within
          (fun child smaller => children child (Nat.le_of_lt smaller)) bodies head
      | true =>
        exact RecursiveNamedCallEvidenceHeads.reflects_at_for functions P transport catalog conditions authorized budget size within
          (fun child smaller => children child (Nat.le_of_lt smaller)) bodies head)

include extension faithful functionLeaves functionTypes missing in
theorem head_reflects_at_with [FunctionCalls.FaultTokens faults] (authenticated : Bool)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.ReflectsAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix))
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head (RecursiveNamedCallEvidenceHeads.Calls (if authenticated then some evidence else none) headers compilation source context)
        values source context reasonAt certificate) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  head_reflects_at_with_for functions extension faithful functionLeaves functionTypes evidence missing
    _ entry_transport (fun entry => entry) (fun _ => fun {_ _ _ _ _ _ _ _ _ _ _ _} _ => True)
    (fun _ _ => by unfold BodyAuthorization; intros; trivial) authenticated budget size within children
    (by
      intro header member child smaller arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry result after _ trace
      exact bodies header member child smaller entry trace)

include extension faithful functionLeaves functionTypes missing in
/-- Original native children select their own pointwise obligations. Reflection
constructs a separately measured source trace. -/
theorem head_reflects_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.ReflectsAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix))
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head (RecursiveNamedCatalog.Head headers compilation source context)
        values source context reasonAt certificate) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  head_reflects_at_with functions extension faithful functionLeaves functionTypes evidence missing false budget size within children bodies

include extension faithful functionLeaves functionTypes unique uninitialized missing in
/-- Structural induction closes every expression child of the same Tree. The
remaining catalog-body Below family is the explicit mutual-induction boundary. -/
theorem preserves_at_with_literals_with_for [FunctionCalls.FaultTokens faults] (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (P : ProtectedExpressionMeaning.Entry)
    (literalMeaning : GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (heads : ∀ certificate child, child ≤ budget →
      (∀ smaller, smaller ≤ budget → RecursiveNamedBoundedContracts.PreservesAt smaller
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults P) →
      RecursiveNamedBoundedContracts.PreservesAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
        (CompatibleExpressionCalls.Head calls values source context reasonAt certificate) faults P) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := calls)
      (fuel := fuel) (values := values) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults
      P := by
  apply fold_contract_at_with_literals calls
    (fun child certificate => RecursiveNamedBoundedContracts.PreservesAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults P)
    (fun meaning _ _ _ certified _ _ _ point => by
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact meaning certified)
    (fun meanings scope id lowered certified => meanings certified ⟨rfl, rfl, rfl⟩)
    budget size within
  · intro child childWithin
    exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed P
        (CompatibleExpressionBuiltins.preserves_with_literals functions extension faithful functionLeaves functionTypes
          program evidence unique uninitialized missing literalMeaning)) child
  · exact heads

include extension faithful functionLeaves functionTypes unique owners uninitialized missing in
theorem preserves_at_with_literals_with [FunctionCalls.FaultTokens faults] (authenticated : Bool)
    (idsUnique : authenticated = true → RequirementIdsUnique context)
    (literalMeaning : GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := RecursiveNamedCallEvidenceHeads.Calls (if authenticated then some evidence else none) headers compilation source context)
        (fuel := fuel) (values := values) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  preserves_at_with_literals_with_for functions extension faithful functionLeaves functionTypes evidence unique uninitialized missing
    _ _ literalMeaning budget size within
    (fun _ child childWithin children => head_preserves_at_with functions extension faithful functionLeaves functionTypes evidence unique owners missing authenticated idsUnique budget child childWithin children bodies)

include extension faithful functionLeaves functionTypes unique owners uninitialized missing in
/-- Structural induction closes every expression child of the same Tree. The
remaining catalog-body Below family is the explicit mutual-induction boundary. -/
theorem preserves_at_with_literals [FunctionCalls.FaultTokens faults]
    (literalMeaning : GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := RecursiveNamedCatalog.Head headers compilation source context)
        (fuel := fuel) (values := values) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  preserves_at_with_literals_with functions extension faithful functionLeaves functionTypes evidence unique owners uninitialized missing false (fun impossible => Bool.noConfusion impossible) literalMeaning budget size within bodies

include extension faithful functionLeaves functionTypes valid unique owners uninitialized missing in
/-- Structural induction closes every expression child of the same Tree. The
remaining catalog-body Below family is the explicit mutual-induction boundary. -/
theorem preserves_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head headers compilation source context)
        fuel values source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  intro scope id lowered tree
  exact preserves_at_with_literals functions extension faithful functionLeaves functionTypes evidence unique owners uninitialized missing
    (CompatibleExpressionLiterals.preserves functions program context evidence valid unique faults) budget size within bodies
    ⟨tree, tree.literalSites⟩

include extension faithful functionLeaves functionTypes unique owners uninitialized missing in
/-- Structural induction closes every expression child of the same Tree. The
remaining catalog-body Below family is the explicit mutual-induction boundary. -/
theorem preserves_at_runtime_with [FunctionCalls.FaultTokens faults] (authenticated : Bool)
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := RecursiveNamedCallEvidenceHeads.Calls (if authenticated then some evidence else none) headers compilation source context)
        (fuel := fuel) (values := values) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  preserves_at_with_literals_with functions extension faithful functionLeaves functionTypes evidence unique owners uninitialized missing authenticated (fun _ => runtime.idsUnique)
    (CompatibleExpressionLiteralRuntime.preserves functions program context evidence sameLedger runtime unique faults) budget size within bodies

include extension faithful functionLeaves functionTypes unique owners uninitialized missing in
/-- Structural induction closes every expression child of the same Tree. The
remaining catalog-body Below family is the explicit mutual-induction boundary. -/
theorem preserves_at_runtime [FunctionCalls.FaultTokens faults]
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := RecursiveNamedCatalog.Head headers compilation source context)
        (fuel := fuel) (values := values) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  preserves_at_runtime_with functions extension faithful functionLeaves functionTypes evidence unique owners uninitialized missing false sameLedger runtime budget size within bodies

include extension faithful functionLeaves functionTypes uninitialized missing in
/-- Reflection uses the same structural Tree, with original native bounds and
independent source costs. No source body trace is an input. -/
theorem reflects_at_with_literals_with_for [FunctionCalls.FaultTokens faults] (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (P : ProtectedExpressionMeaning.Entry)
    (literalMeaning : GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (heads : ∀ certificate child, child ≤ budget →
      (∀ smaller, smaller ≤ budget → RecursiveNamedBoundedContracts.ReflectsAt smaller
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults P) →
      RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
        (CompatibleExpressionCalls.Head calls values source context reasonAt certificate) faults P) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := calls)
      (fuel := fuel) (values := values) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults
      P := by
  apply fold_contract_at_with_literals calls
    (fun child certificate => RecursiveNamedBoundedContracts.ReflectsAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults P)
    (fun meaning _ _ _ certified _ _ _ point => by
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact meaning certified)
    (fun meanings scope id lowered certified => meanings certified ⟨rfl, rfl, rfl⟩)
    budget size within
  · intro child childWithin
    exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed P
        (CompatibleExpressionBuiltins.reflects_with_literals functions extension faithful functionLeaves functionTypes
          program evidence uninitialized missing literalMeaning)) child
  · exact heads

include extension faithful functionLeaves functionTypes uninitialized missing in
theorem reflects_at_with_literals_with [FunctionCalls.FaultTokens faults] (authenticated : Bool)
    (literalMeaning : GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := RecursiveNamedCallEvidenceHeads.Calls (if authenticated then some evidence else none) headers compilation source context)
        (fuel := fuel) (values := values) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  reflects_at_with_literals_with_for functions extension faithful functionLeaves functionTypes evidence uninitialized missing
    _ _ literalMeaning budget size within
    (fun _ child childWithin children => head_reflects_at_with functions extension faithful functionLeaves functionTypes evidence missing authenticated budget child childWithin children bodies)

include extension faithful functionLeaves functionTypes uninitialized missing in
/-- Reflection uses the same structural Tree, with original native bounds and
independent source costs. No source body trace is an input. -/
theorem reflects_at_with_literals [FunctionCalls.FaultTokens faults]
    (literalMeaning : GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := RecursiveNamedCatalog.Head headers compilation source context)
        (fuel := fuel) (values := values) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  reflects_at_with_literals_with functions extension faithful functionLeaves functionTypes evidence uninitialized missing false literalMeaning budget size within bodies

include extension faithful functionLeaves functionTypes valid uninitialized missing in
/-- Reflection uses the same structural Tree, with original native bounds and
independent source costs. No source body trace is an input. -/
theorem reflects_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head headers compilation source context)
        fuel values source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  intro scope id lowered tree
  exact reflects_at_with_literals functions extension faithful functionLeaves functionTypes evidence uninitialized missing
    (CompatibleExpressionLiterals.reflects functions program context evidence valid source faults) budget size within bodies
    ⟨tree, tree.literalSites⟩

include extension faithful functionLeaves functionTypes uninitialized missing in
/-- Reflection uses the same structural Tree, with original native bounds and
independent source costs. No source body trace is an input. -/
theorem reflects_at_runtime_with [FunctionCalls.FaultTokens faults] (authenticated : Bool)
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := RecursiveNamedCallEvidenceHeads.Calls (if authenticated then some evidence else none) headers compilation source context)
        (fuel := fuel) (values := values) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  reflects_at_with_literals_with functions extension faithful functionLeaves functionTypes evidence uninitialized missing authenticated
    (CompatibleExpressionLiteralRuntime.reflects functions program context evidence sameLedger runtime source faults) budget size within bodies

include extension faithful functionLeaves functionTypes uninitialized missing in
/-- Reflection uses the same structural Tree, with original native bounds and
independent source costs. No source body trace is an input. -/
theorem reflects_at_runtime [FunctionCalls.FaultTokens faults]
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := RecursiveNamedCatalog.Head headers compilation source context)
        (fuel := fuel) (values := values) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  reflects_at_runtime_with functions extension faithful functionLeaves functionTypes evidence uninitialized missing false sameLedger runtime budget size within bodies

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionTreeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageScopes
/-! The real named codebook entry selects the original analyzed sidecar for
the actual specialized source view. The registry also retains the existing
anonymous selections. This is static invocation provenance; it supplies no
body execution law or native closure capture relation. Method scopes additionally retain independent trait-method selection; their
synthetic compiler rows do not assert ordinary declaration authority. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageScopes
open Frontend SourceInference SourceCoreStageContracts
open CallContractCertificates CallEntryCertificates

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- This compares the complete selected specialization, rather than its key
or erased parameter/result types. -/
theorem sidecar_caller {plan : Plan} {key : Key} {sidecar : Sidecar}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : prepareSidecar plan key = .ok sidecar)
    (selected : SourceCompilationPlan.exactSpecialization plan key = .ok row) :
    sidecar.caller = row := by
  unfold prepareSidecar at prepared
  simp only [selected, Except.mapError, bind, Except.bind] at prepared
  obtain ⟨_, _, prepared⟩ := bind_ok prepared
  split at prepared
  · cases prepared
  · split at prepared
    · cases prepared; rfl
    · cases prepared

inductive Selected (compiled : SourceCoreUnifiedCompilation.Compiled)
    (native : SourceCoreGeneralFunctions.CallableContext) :
    Dynamic.Closure → Staging.Recursive.Scope → Prop where
  | anonymous {function : Dynamic.Closure} {scope : Staging.Recursive.Scope}
      (receipt : RecursiveStageRegistry.Selected compiled.sourceProgram compiled.indexed.base.plan native.table function scope) :
      Selected compiled native function scope
  | named {row : SourceSpecialization.SpecializedFunction}
      (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
      (sidecar : Sidecar)
      (issued : prepareSidecar compiled.indexed.base.plan row.key = .ok sidecar)
      (same : sidecar.caller = row) :
      Selected compiled native prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view)

  | method {method : ExecutableImplMethods.CheckedMethod}
      {callerContext : SourceSemantics.Context} {callerEvidence dictionary : Dynamic.EvidenceEnvironment}
      {traitName methodName : String} {requirements : List RequirementId} {roots : List StatementId}
      (selection : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram)
        callerContext callerEvidence traitName methodName requirements
        (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method) dictionary)
      (statements : Dynamic.StatementRoots method.specialized.function.typedBody.roots roots)
      (sidecar : Sidecar)
      (issued : prepareSidecar compiled.indexed.base.plan method.specialized.key = .ok sidecar)
      (same : sidecar.caller = method.specialized) :
      Selected compiled native
        (Staging.Recursive.methodView (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method) dictionary roots)
        (RecursiveStageRegistry.scope sidecar []
          (Staging.Recursive.methodView (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method) dictionary roots))

/-- All cases use the same actual artifact and original plan. The prepared
table equation is kept with the registry, so an arbitrary table is not used
as the public invocation registry. -/
def registry {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (_actual : RecursiveNamedPreparedStageContracts.Prepared compiled native) : Staging.Recursive.Registry where
  Closure := Selected compiled native
  source := by
    intro function scope related
    cases related with
    | anonymous receipt => exact (RecursiveStageRegistry.registry _ _ _).source receipt
    | named => rfl
    | method => rfl
  context := by
    intro function scope related
    cases related with
    | anonymous receipt => exact (RecursiveStageRegistry.registry _ _ _).context receipt
    | named => rfl
    | method => rfl
  evidence := by
    intro function scope related
    cases related with
    | anonymous receipt => exact (RecursiveStageRegistry.registry _ _ _).evidence receipt
    | named => rfl
    | method => rfl

section Actual
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {native : SourceCoreGeneralFunctions.CallableContext}
  (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan row.key = .ok row)
  (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named row.key))

include actual prepared record descriptor in
/-- The descriptor's authenticated named contract supplies its real sidecar.
The complete plan record identifies that sidecar with the actual source view's
specialization, including all original stage flags and solved requirements. -/
theorem selected_of_descriptor :
    ∃ sidecar : Sidecar,
      prepareSidecar compiled.indexed.base.plan row.key = .ok sidecar ∧ sidecar.caller = row ∧
      (registry actual).Closure prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view) := by
  obtain ⟨entry, member, origin, _⟩ := descriptor_entry descriptor
  have authenticated := actual.entries_authenticated entry member
  unfold CallEntryCertificates.Authenticated at authenticated
  rw [origin] at authenticated
  generalize count_eq : entry.parameterCount = count at authenticated
  generalize contract_eq : entry.contract = contract at authenticated
  cases authenticated with
  | named issued =>
    obtain ⟨receipt⟩ := named_of_accepted issued
    have same := sidecar_caller receipt.prepared record
    exact ⟨receipt.sidecar, receipt.prepared, same, .named prepared receipt.sidecar receipt.prepared same⟩

include actual prepared record descriptor in
/-- The scope retains the exact original analysis and both substitution
components. Named views have no lexical local instantiation. -/
theorem original_stages :
    ∃ sidecar : Sidecar,
      (registry actual).Closure prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view) ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).origin.declarationSubstitution = row.parameterSubstitution ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).origin.localSubstitution = [] ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).guards.stages.callerReturnComptime = row.function.returnComptime ∧
      SourceStageAnalysis.analyzeFunction row.function = .ok row.stageAnalysis := by
  obtain ⟨sidecar, _, same, selected⟩ := selected_of_descriptor actual prepared record descriptor
  exact ⟨sidecar, selected, by simp only [RecursiveStageRegistry.scope_declarationSubstitution, same],
    rfl, by simp only [RecursiveStageRegistry.scope_returnMarker, same], by simpa only [same] using sidecar.analyzed⟩

include actual prepared record descriptor in
/-- The full resolved source evidence is passed to the callee scope without
recomputing it from a descriptor or native type. -/
theorem evidence_preserved :
    ∃ sidecar : Sidecar,
      (registry actual).Closure prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view) ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).evidence =
        CallableNamedMetadata.environment prepared.available := by
  obtain ⟨sidecar, _, _, selected⟩ := selected_of_descriptor actual prepared record descriptor
  exact ⟨sidecar, selected, rfl⟩

include actual prepared record descriptor in
/-- Independent source validity provides the invocation frame and covers the
complete evidence context. Table authentication itself supplies no typing. -/
theorem source_frame_preserved
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    ∃ sidecar : Sidecar,
      (registry actual).Closure prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view) ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).source = row.function.typedBody ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).context =
        (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row).context ∧
      prepared.view.evidence.Covers (RecursiveStageRegistry.scope sidecar [] prepared.view).context ∧
      Staging.FunctionHasStages row.function := by
  obtain ⟨sidecar, _, _, selected⟩ := selected_of_descriptor actual prepared record descriptor
  have frame := prepared.source_frame wellFormed range
  exact ⟨sidecar, selected, frame.source, frame.context, by change Dynamic.EvidenceEnvironment.Covers prepared.view.context prepared.view.evidence; rw [frame.context]; exact frame.covers,
    prepared.has_stages wellFormed⟩

include actual prepared descriptor in
/-- The named descriptor's static origin is attached to the same generic
instantiation and full resolved evidence. The underlying native code/capture
meaning is an additional payload relation, independent of this receipt. -/
theorem global_origin
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key) (raw : Core.Value) :
    CallableLedger.OriginRep compiled.indexed.base.plan native.table
      (.global ⟨CallableNamedMetadata.instantiation row, prepared.view.evidence⟩)
      (.pair raw (.word descriptor.id)) :=
  RecursiveStageProjection.named_origin (function := ⟨CallableNamedMetadata.instantiation row, prepared.view.evidence⟩) actual.accepted descriptor target raw
end Actual

/-- Existing anonymous factory selections remain available in the same
registry. Their full cumulative local substitution is unchanged. -/
theorem anonymous_preserved {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    {function : Dynamic.Closure} {scope : Staging.Recursive.Scope}
    (selected : RecursiveStageRegistry.Selected compiled.sourceProgram compiled.indexed.base.plan native.table function scope) :
    (registry actual).Closure function scope := .anonymous selected

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageScopes
end

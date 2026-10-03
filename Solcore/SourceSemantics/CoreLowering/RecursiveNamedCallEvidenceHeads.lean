import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionHeadBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedCallEvidence
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCertificateNativeTyping

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
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  intro scope id lowered head
  cases head with
  | ordinary ordinary =>
    exact RecursiveNamedExpressionHeadBounds.preserves_at functions budget size within unique owners argumentMeaning bodyMeaning ordinary
  | @direct compilerProgram project caller child fuel id callee arguments instantiation reasonAt policy node output header receipt certified metadata =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees typed installed trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨callerEntry⟩ := installed
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
      RecursiveNamedExpressionHeadBounds.call_preserves_bounded functions certified.sequence certified.nativeTypes packed budget
        argumentMeaning (bodyMeaning header certified.selected.member) owners certified.selected.member
        callerEntry environments heaps locals agrees typed independent within
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, preserved, heapMetadata⟩
    · change Evaluates actual store (lowered.expression.rename ξ) value finalStore
      rw [certified.emitted receipt metadata.coercions]
      simpa only [NamedCalls.Arguments.call_rename] using evaluated
    · simpa only [certified.sourceType, (congrArg (fun code : Lowered => code.type) (certified.emitted receipt metadata.coercions))] using represented

/-- Reflection consumes the original completed call and its strict native
children. Its source grade and authenticated dictionary remain independent. -/
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (argumentMeaning : RecursiveNamedBoundedContracts.Below budget (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source children faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix)))
    (bodyMeaning : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head headers compilation source context evidence children) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  intro scope id lowered head
  cases head with
  | ordinary ordinary =>
    exact RecursiveNamedExpressionHeadBounds.reflects_at functions budget size within argumentMeaning bodyMeaning ordinary
  | @direct compilerProgram project caller child fuel id callee arguments instantiation reasonAt policy node output header receipt certified metadata =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees typed installed evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨callerEntry⟩ := installed
    have emitted := certified.emitted receipt metadata.coercions
    change EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore at evaluated
    rw [emitted] at evaluated
    simp only [NamedCalls.Arguments.call_rename] at evaluated
    have packed : header.named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
      simpa only [certified.selected.signature] using receipt.native.inputType
    obtain ⟨traceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preserved, heapMetadata, _⟩ :=
      RecursiveNamedExpressionHeadBounds.call_reflects_bounded functions certified.sequence certified.nativeTypes packed budget
        argumentMeaning (bodyMeaning header certified.selected.member) certified.selected.member
        callerEntry environments heaps locals agrees typed evaluated within
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
theorem native {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {children : GenericExpressionMeaning.Certificate} {administrative : Core.Context}
    (slots : ∀ header, header ∈ headers → administrative[compilation.administrativePrefix + header.slot]? =
      some header.named.signature.referenceType)
    (head : Head headers compilation source context evidence children scope id output)
    (typed : ∀ child code, children scope child code →
      CompatibleExpressionScalarNativeTyping.NativeTyping values.checked.catalog.definitions
        (SourceCoreLocalCell.coreContext scope ++ administrative) code) :
    CompatibleExpressionScalarNativeTyping.NativeTyping values.checked.catalog.definitions
      (SourceCoreLocalCell.coreContext scope ++ administrative) output := by
  cases head with
  | ordinary ordinary =>
    cases ordinary with
    | @named callee arguments body node calleeNode name codes expression member metadata sourceType form calleeFound calleeForm
        calleeRequirements calleeCoercions valid predicates evidence arity emission selectedSlot sequence nativeTypes =>
      have packed := CompatibleExpressionConstructorNativeTyping.packed_native sequence typed
      have equation := emission.equation
      have resultWF := CompatibleExpressionCertificateNativeTyping.project_wellFormed metadata.projected
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
    have resultWF := CompatibleExpressionCertificateNativeTyping.project_wellFormed metadata.projected
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

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallEvidenceHeads

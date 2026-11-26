import Solcore.SourceSemantics.CoreLowering.AcceptedCalls

/-!
# Accepted bodies: a named function used as a value

A declaration reference that is not a direct call's callee, such as the
initializer `identity` of `let f: function(word) returns (word) = identity;`.
The named policy lowers it through its plan's reference edge to the decorated
read of the selected header's global cell (`namedReference`). This module gives
its compiler receipt, the call authority of its selected header, the value
heads on the `CellAwareInvocationExpressionBounds` protocol and the lifting of
the Source's `declaration` rule to the staged atomic value. Nothing uses them yet:
the nested expression family takes them with the indirect calls.

Main declarations: `CellAwareInvocationAcceptedValueSites.ValueSite`,
`CellAwareNamedValueCertificates.Receipt` and `Receipt.of_site`,
`CellAwareNamedValueAuthority.Port`, `CellAwareNamedValuePorts.ports`,
`CellAwareInvocationNamedValueBounds.preserves` and `reflects`, and
`CellAwareInvocationAcceptedValueLifting.value_lift` and `value_lift_fault`.
-/

section
/-! A named function value of a named-row body: a declaration reference with
no coercions or requirements, that is not a generalized initializer, of a
monomorphic instantiation, in a row without evidence assumptions. Unlike a
`ReferenceSite`, the plan may record its reference edge; the named policy's
special callback declines it and its read policy is the compatible reader. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedValueSites
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context representation)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Monomorphic)

/-- A named function value of a named-row body. -/
structure ValueSite {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) where
  node : ExpressionNode
  name : String
  instantiation : DeclarationInstantiation
  found : source.lookupExpression? id = some node
  form : node.form = .reference name (.declaration instantiation)
  coercions : node.coercions = []
  requirements : node.requirements = []
  notInitializer : prepared.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none
  monomorphic : Monomorphic instantiation
  assumptions : named.specialized.assumptions = []

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {id : ExpressionId}

theorem contextual (site : ValueSite prepared named source id) :
    SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      (context prepared named).plan prepared.base.locals named.signature.key none source id = .ok source := by
  simp [SourceCoreGeneralFunctions.contextualSource, site.found, site.form]

private theorem evidence_none (site : ValueSite prepared named source id)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none := by
  simp [SourceCoreEvidence.lowerWithProjector, site.found, site.form, site.requirements, site.coercions,
    site.assumptions]

variable {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : Compilation prepared named diagnostics code)

/-- The named policy's special callback declines a value site. -/
theorem special (site : ValueSite prepared named source id) (rootFuel : Nat)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok none := by
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  have ownerEq : (context prepared named).owner = named.signature.key := rfl
  simp only [ownerEq, contextual site, bind, Except.bind, pure, Except.pure, site.found,
    site.notInitializer, Option.filter_none]
  rw [evidence_none site child budget scope reasonAt]
  simp [site.form]

theorem read (site : ValueSite prepared named source id) (rootFuel : Nat) :
    (namedPolicy compiled rootFuel).readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  simp only [namedPolicy, contextual site, bind, Except.bind]
  rfl

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedValueSites
end

section
/-! The compiler receipt of a named function value. The accepted lowering of
`.reference _ (.declaration …)` selects the plan's reference edge and the
header's global slot (`selectedSignature … true`), checks the node's native
type against the callable function type, numbers the slot and decorates the
optional-cell read of the slot (`namedReference`) with the descriptor of the
callable codebook's `.named` row. The receipt retains each of these, and the
shape of the selected function type, which the compiler matched. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedValueCertificates
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Compilation context)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Monomorphic)
open CellAwareInvocationAcceptedValueSites (ValueSite)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

private theorem ensure_type {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at accepted

/-- The accepted selection matched the selected row's function type. -/
theorem selected_signature_shape
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {instantiation : DeclarationInstantiation}
    {isReference : Bool} {index : Nat} {signature : SourceCoreCalls.Signature}
    (accepted : SourceCoreFunctions.selectedSignature policy compilation source node instantiation isReference =
      .ok (index, signature)) :
    ∃ specialized parameter result,
      SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok specialized ∧
      specialized.function.type = .function parameter result := by
  unfold SourceCoreFunctions.selectedSignature at accepted
  by_cases owner : source.owner = compilation.owner.declaration
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte] at accepted
    obtain ⟨caller, callerReceipt, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨target, targetReceipt, accepted⟩ := bind_ok accepted
      obtain ⟨key, edgeReceipt, accepted⟩ := bind_ok accepted
      obtain ⟨specialized, specializationReceipt, accepted⟩ := bind_ok accepted
      split at accepted
      · split at accepted
        · cases accepted
        · split at accepted
          all_goals simp only [pure, Except.pure, bind, Except.bind] at accepted
          all_goals try contradiction
          rename_i parameter result shape
          obtain ⟨_, _, accepted⟩ := bind_ok accepted
          obtain ⟨_, _, accepted⟩ := bind_ok accepted
          obtain ⟨selection, globalReceipt, accepted⟩ := bind_ok accepted
          rcases selection with ⟨selectedIndex, selectedSignature⟩
          obtain ⟨_, _, accepted⟩ := bind_ok accepted
          obtain ⟨_, _, accepted⟩ := bind_ok accepted
          cases accepted
          change ((match compilation.globals.zipIdx.filter (fun entry => decide (entry.1.key = key)) with
            | [] => .error (.callPreparation (.missingSpecialization key))
            | [(signature, index)] => .ok (index, signature)
            | candidates => .error (.callPreparation (.duplicateSpecialization key candidates.length))) :
              Except SourceCoreBasic.Error (Nat × SourceCoreCalls.Signature)) =
              .ok (selectedIndex, selectedSignature) at globalReceipt
          split at globalReceipt
          · cases globalReceipt
          · rename_i signature index filtered
            cases globalReceipt
            have member : (selectedSignature, selectedIndex) ∈ compilation.globals.zipIdx.filter
                (fun entry => decide (entry.1.key = key)) := by
              rw [filtered]; exact .head _
            have facts := List.mem_filter.mp member
            have keyEq : selectedSignature.key = key := of_decide_eq_true facts.2
            exact ⟨specialized, parameter, result,
              by simpa only [keyEq] using mapError_ok specializationReceipt, shape⟩
          · cases globalReceipt
      · cases accepted
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
  · simp [owner, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted

/-- An accepted declaration reference retains its selection, its native type
check, its slot number and its decoration request. -/
theorem value_of_accepted
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {name : String} {instantiation : DeclarationInstantiation} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .reference name (.declaration instantiation))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    ∃ index signature identity,
      SourceCoreFunctions.selectedSignature policy compilation source node instantiation true =
        .ok (index, signature) ∧
      type = policy.callables.functionType signature.parameterType signature.resultType ∧
      Word.ofNat? (index + 1) = some identity ∧
      policy.callables.decorateCallable compilation source node (.named signature.key)
        signature.parameterType signature.resultType
        (SourceCoreFunctions.namedReference signature
          (scope.length + compilation.administrativePrefix + index) identity compilation.internalReason) =
        .ok lowered.expression ∧ lowered.type = type := by
  cases hook : policy.lowerSpecial? <;> simp only [hook] at special
  all_goals
    unfold SourceCoreFunctions.lowerExpressionWithPolicy at accepted
    simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, hook,
      bind, Except.bind, pure, Except.pure] at accepted
    try rw [special] at accepted
    simp only [form, read] at accepted
    obtain ⟨selection, selectionReceipt, accepted⟩ := bind_ok accepted
    rcases selection with ⟨index, signature⟩
    obtain ⟨checked, typeReceipt, accepted⟩ := bind_ok accepted
    cases checked
    split at accepted
    · rename_i identity wordReceipt
      obtain ⟨expression, decorated, accepted⟩ := bind_ok accepted
      cases accepted
      exact ⟨index, signature, identity, selectionReceipt, ensure_type typeReceipt, wordReceipt, decorated, rfl⟩
    · simp at accepted

/-- The general callable policy decorates a named reference with the
descriptor of its key's `.named` row, which therefore exists. -/
theorem decoration_of_accepted (native : SourceCoreGeneralFunctions.CallableContext)
    (active : TypeSystem.Substitution) {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {node : ExpressionNode} {signature : SourceCoreCalls.Signature} {index : Nat} {identity : Word}
    {expression : Expr}
    (decorated : (SourceCoreGeneralFunctions.callablePolicy (some native) active).decorateCallable compilation
      source node (.named signature.key) signature.parameterType signature.resultType
      (SourceCoreFunctions.namedReference signature index identity compilation.internalReason) = .ok expression) :
    ∃ descriptor : SourceCoreCallableContracts.Descriptor native.table (.named signature.key),
      expression = LanguageResult.bind (CallableContract.functionType signature.parameterType signature.resultType)
        (SourceCoreFunctions.namedReference signature index identity compilation.internalReason)
        (LanguageResult.success (descriptor.wrap (.var 0))) := by
  cases descriptorFound : SourceCoreCallableContracts.descriptor native.table (.named signature.key) with
  | error error =>
    simp [SourceCoreGeneralFunctions.callablePolicy, descriptorFound, bind, Except.bind, Except.mapError]
      at decorated
  | ok descriptor =>
    rw [NamedCalls.reference_decoration native active compilation source node signature index identity descriptor
      descriptorFound] at decorated
    exact ⟨descriptor, (Except.ok.inj decorated).symm⟩

/-- The compiler receipt of a named function value: the selected global slot
and specialization, the shape of its function type, the slot's number, the
descriptor of its `.named` codebook row and the emitted decorated read. -/
structure Receipt (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (compilation : SourceCoreFunctions.Context) (values : SourceCoreCompatibleValues.Context)
    (table : SourceCoreStageCodebook.Table) (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr) where
  node : ExpressionNode
  name : String
  instantiation : DeclarationInstantiation
  metadata : CompatibleExpressionReads.Metadata values.checked source id node lowered.type
  form : node.form = .reference name (.declaration instantiation)
  monomorphic : Monomorphic instantiation
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
    compilation source scope id reasonAt = .ok lowered
  index : Nat
  signature : SourceCoreCalls.Signature
  specialized : SourceSpecialization.SpecializedFunction
  parameter : TypeSystem.Ty
  result : TypeSystem.Ty
  target : SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation = .ok signature.key
  global : compilation.globals[index]? = some signature
  record : SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok specialized
  shape : specialized.function.type = .function parameter result
  identity : Word
  number : Word.ofNat? (index + 1) = some identity
  descriptor : SourceCoreCallableContracts.Descriptor table (.named signature.key)
  nativeType : lowered.type = CallableContract.functionType signature.parameterType signature.resultType
  emitted : lowered.expression = LanguageResult.bind
    (CallableContract.functionType signature.parameterType signature.resultType)
    (SourceCoreFunctions.namedReference signature (scope.length + compilation.administrativePrefix + index)
      identity compilation.internalReason)
    (LanguageResult.success (descriptor.wrap (.var 0)))

/-- The original compatible reader and the accepted lowering under a general
callable policy supply the complete receipt. -/
theorem Receipt.of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode} {name : String}
    {instantiation : DeclarationInstantiation} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.declaration instantiation))
    (monomorphic : Monomorphic instantiation)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    Nonempty (Receipt policy body fuel compilation values native.table source scope id reasonAt lowered) := by
  have original := accepted
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
        compilation childSource childScope childId childReasonAt) (fuel + 1)
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      simp only [form] at accepted
      obtain ⟨pair, read, _remaining⟩ := bind_ok accepted
      rcases pair with ⟨other, type⟩
      have metadata := CompatibleExpressionReads.metadata_of_read (readPolicy.symm ▸ read)
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst other
      obtain ⟨index, signature, identity, selection, typeEq, number, decorated, loweredType⟩ :=
        value_of_accepted owner found read form (special _ _) original
      obtain ⟨target, global⟩ := NamedCalls.selected_signature_target selection
      obtain ⟨specialized, parameter, result, record, shape⟩ := selected_signature_shape selection
      rw [callables] at decorated typeEq
      obtain ⟨descriptor, emitted⟩ := decoration_of_accepted native active decorated
      exact ⟨⟨node, name, instantiation, loweredType ▸ metadata, form, monomorphic, original, index, signature,
        specialized, parameter, result, target, global, record, shape, identity, number, descriptor,
        loweredType.trans typeEq, emitted⟩⟩
  · simp [owner, bind, Except.bind] at accepted

/-- A value site of a named row and its accepted lowering under the named
policy supply the receipt at the callable codebook of the indexed program. -/
theorem Receipt.of_site {whole : SourceCoreUnifiedCompilation.Compiled}
    {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {code : Expr} (generation : Compilation whole.indexed named diagnostics code) (rootFuel : Nat)
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (site : ValueSite whole.indexed named source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy generation rootFuel)
      (namedLowerBody generation) (fuel + 1) (context whole.indexed named) source scope id reasonAt = .ok lowered) :
    Nonempty (Receipt (namedPolicy generation rootFuel) (namedLowerBody generation) fuel
      (context whole.indexed named) (.initial whole.compatible.checked)
      whole.indexed.ancestry.graph.inputs.callable.table source scope id reasonAt lowered) :=
  Receipt.of_functions whole.indexed.ancestry.graph.inputs.callable []
    (CellAwareNamedCallPorts.callable_policy generation) site.found site.form site.monomorphic
    (fun child budget => CellAwareInvocationAcceptedValueSites.special generation site rootFuel child budget
      scope reasonAt)
    (CellAwareInvocationAcceptedValueSites.read generation site rootFuel) accepted

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedValueCertificates
end

section
/-! Static authority of a named function value, as
`CallableIndexedOwnedPreparedStagedDirectCallAuthority` gives a direct call's:
the receipt's slot and signature select a header of a finite inventory, whose
preparation, alignment and Source function the port retains. The value's
Source dictionary is empty: its instantiation is monomorphic. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedValueAuthority
open Core Frontend SourceInference
open CellAwareNamedValueCertificates (Receipt)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {table : SourceCoreStageCodebook.Table} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation values table source scope id reasonAt lowered)

structure Ready (catalog : List (CallableIndexedOwnedFunctionValues.Header compiled program)) where
  header : CallableIndexedOwnedFunctionValues.Header compiled program
  member : header ∈ catalog
  slot : header.slot = receipt.index
  signature : header.named.signature = receipt.signature
  specialized : header.named.specialized = receipt.specialized
  metadata : receipt.instantiation = header.instantiation

/-- The covering header of the selected slot has the receipt's complete
metadata, as for a direct call. -/
theorem Ready.of_slot
    {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    (covered : ∃ header ∈ catalog,
      header.slot = receipt.index ∧ header.named.signature = receipt.signature)
    (plan : compilation.plan = compiled.indexed.base.plan)
    (ordered : ∀ header, header ∈ catalog →
      header.instantiation.parameterSubstitution.map Prod.fst =
        (header.named.specialized.parameterSubstitution.map Prod.fst).reverse) :
    Nonempty (Ready receipt catalog) := by
  obtain ⟨header, member, slot, signature⟩ := covered
  have record := CallableIndexedActualNamedSourceReceipts.header_record compiled header
  rw [signature, ← plan] at record
  have specialized : header.named.specialized = receipt.specialized :=
    Except.ok.inj (record.symm.trans receipt.record)
  have occurrence := CallableNamedMetadata.matches_of_exact receipt.target receipt.record
  have headerTarget := header.target
  rw [signature, ← plan] at headerTarget
  have headerMatch := CallableNamedMetadata.matches_of_exact headerTarget receipt.record
  have occurrenceEq := occurrence.retained_canonical
    ((receipt.monomorphic.ordinary compilation.plan).ordered _ _ receipt.target receipt.record)
  have headerEq := headerMatch.retained_canonical (by
    simpa only [← specialized] using ordered header member)
  exact ⟨⟨header, member, slot, signature, specialized, occurrenceEq.trans headerEq.symm⟩⟩

/-- A selected finite row with its preparation, its reissued header and its
Source function. -/
structure Port (catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram))) extends Ready receipt catalog where
  row : SourceSpecialization.SpecializedFunction
  prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row
  aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared receipt.instantiation toReady.header
  rawDictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment
  function : Dynamic.GlobalFunction
  sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt toReady.header rawDictionary function
  sourceInstantiation : function.instantiation = receipt.instantiation
  dictionary : function.evidence = prepared.view.evidence

/-- The retained inventory supplies the port of every covered slot. -/
theorem Port.of_inventory_at {inputs : List (Input compiled)} (rows : Inventory inputs)
    (covered : ∃ header ∈ headers rows,
      header.slot = receipt.index ∧ header.named.signature = receipt.signature)
    (plan : compilation.plan = compiled.indexed.base.plan) :
    Nonempty (Port receipt (headers rows)) := by
  obtain ⟨ready⟩ := Ready.of_slot receipt covered plan
    (CallableIndexedOwnedPreparedFiniteNamedInventories.ordered rows)
  obtain ⟨input, packet, _retained, same⟩ := rows.mem_headers ready.header ready.member
  have aligned := packet.aligned
  have metadata : (CallableNamedCanonicalOrder.retainedInstantiation input.row) = receipt.instantiation :=
    aligned.metadata.symm.trans ((congrArg (·.instantiation) same).trans ready.metadata.symm)
  have aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt
      (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
      receipt.instantiation ready.header := by
    rw [← same, ← metadata]
    exact aligned
  have sourceAt := packet.sourceAt
  have sourceMetadata :
      (CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized
        input.prepared.available)).instantiation = receipt.instantiation := by
    change CallableNamedCanonicalOrder.retainedInstantiation packet.header.named.specialized = receipt.instantiation
    rw [packet.aligned.named]
    change CallableNamedCanonicalOrder.retainedInstantiation input.prepared.named.specialized = receipt.instantiation
    rw [input.prepared.same]
    exact metadata
  refine ⟨{ toReady := ready
            row := input.row
            prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected
            aligned := aligned
            rawDictionary := input.prepared.available
            function := CallableNamedReversal.global
              (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available)
            sourceAt := same ▸ sourceAt
            sourceInstantiation := sourceMetadata
            dictionary := (same ▸ sourceAt).dictionary.symm.trans
              (congrArg Dynamic.Closure.evidence aligned.function) }⟩

variable {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
  (Program.ofChecked compiled.sourceProgram))}

/-- A monomorphic value's selected row has no assumptions, so its prepared
dictionary is empty. -/
theorem Port.evidence_empty (port : Port receipt catalog) : port.function.evidence = [] := by
  have same : port.row = receipt.specialized :=
    port.prepared.same.symm.trans
      ((congrArg (fun named => named.specialized) port.aligned.named).symm.trans port.specialized)
  have metadata := CallableNamedMetadata.matches_of_exact receipt.target receipt.record
  have assumptions : port.row.assumptions = [] := by
    rw [same]
    exact metadata.predicates.trans receipt.monomorphic.predicates
  exact port.dictionary.trans (RecursiveNamedPreparedHeaders.Prepared.evidence_empty port.prepared assumptions)

/-- The Source value of the reference is the port's global function. -/
theorem Port.global_eq (port : Port receipt catalog) :
    Dynamic.Value.global ⟨receipt.instantiation, []⟩ = .global port.function := by
  have metadata := port.sourceInstantiation
  have empty := port.evidence_empty
  cases h : port.function with
  | mk actual actualEvidence =>
    simp only [h] at metadata empty
    cases metadata
    cases empty
    rfl

/-- The reference's Source type is the selected row's function type. -/
theorem Port.instantiation_type (port : Port receipt catalog) :
    receipt.instantiation.type = port.header.named.specialized.function.type := by
  rw [← port.sourceInstantiation, port.sourceAt.retained]
  rfl

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedValueAuthority
end

section
/-! The value ports of a named row from a complete inventory, as
`CellAwareInvocationAcceptedCallAuthority.ports` gives the direct calls'. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedValuePorts
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Compilation context)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)
open CellAwareNamedValueCertificates (Receipt)
open CellAwareNamedValueAuthority (Port)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}

/-- Every value receipt of the named row's compiler selects a header of the
catalog. -/
def ValuePorts (generation : Compilation whole.indexed named diagnostics code)
    (catalog : List (CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram))) :
    Prop :=
  ∀ {rootFuel fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt (namedPolicy generation rootFuel) (namedLowerBody generation) fuel
      (context whole.indexed named) (.initial whole.compatible.checked)
      whole.indexed.ancestry.graph.inputs.callable.table source scope id reasonAt lowered),
    Nonempty (Port receipt catalog)

/-- A complete inventory covers every value receipt's slot. -/
theorem ports {inputs : List (Input whole)} (rows : Inventory inputs)
    (complete : ∀ {index : Nat} {function : SourceCoreGeneralFunctions.Function},
      whole.indexed.base.functions[index]? = some function →
      ∃ input ∈ inputs, input.prepared.index = index ∧ input.prepared.named = function)
    (generation : Compilation whole.indexed named diagnostics code) :
    ValuePorts generation (headers rows) := by
  intro rootFuel fuel source scope id reasonAt lowered receipt
  have global : whole.indexed.base.globals[receipt.index]? = some receipt.signature := receipt.global
  rw [CallableIndexedPreparedInventories.cached_globals whole, List.getElem?_map, Option.map_eq_some_iff] at global
  obtain ⟨function, functionFound, signatureEq⟩ := global
  obtain ⟨input, member, slot, namedEq⟩ := complete functionFound
  obtain ⟨issued, retained⟩ := rows.row_at input member
  exact CellAwareNamedValueAuthority.Port.of_inventory_at receipt rows
    ⟨issued.header, CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory.header_member retained,
      issued.aligned.slot.trans slot,
      (congrArg (·.signature) issued.aligned.named).trans ((congrArg (·.signature) namedEq).trans signatureEq)⟩
    rfl

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedValuePorts
end

section
/-! The value heads of a named function value: a pure leaf, like a builtin
value. The Source's `declaration` rule gives `.global ⟨instantiation, []⟩`
and leaves the heap. The emitted decorated read loads the selected header's
global cell, which the caller's slot receipt names and whose installed closure
the cache authority fixes; the carrier is the positive named handle of
`CallableIndexedOwnedPhysicalNamedAssociation`, and the function model
represents it (`NamedValuesIncluded`), as the root model does
(`included_root`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationNamedValueBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey NamedSourceAt NamedInstalledCode)
open CallableIndexedOwnedPreparedStagedPhysicalDirectHeadBounds (Point)
open CellAwareNamedValueCertificates (Receipt)
open CellAwareNamedValueAuthority (Port)
universe u

/-- The function model represents every positive named handle. -/
def NamedValuesIncluded {compiled : SourceCoreUnifiedCompilation.Compiled}
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) : Prop :=
  ∀ {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {function : Dynamic.GlobalFunction} {native : Value} {type : Ty},
    CallableIndexedOwnedPhysicalNamedAssociation.StaticMember headers keys mapping world sourceType function native
      type →
    functions.Represents registry mapping world sourceType (.global function) native type

/-- The root function model of the accepted family represents them. -/
theorem included_root {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    NamedValuesIncluded headers keys
      (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry faults profile) :=
  fun member => .ordinary (.global member)

theorem emitted_rename {table : SourceCoreStageCodebook.Table} (signature : SourceCoreCalls.Signature)
    (position : Nat) (identity reason : Word)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.named signature.key)) (ξ : Renaming) :
    (LanguageResult.bind (CallableContract.functionType signature.parameterType signature.resultType)
      (SourceCoreFunctions.namedReference signature position identity reason)
      (LanguageResult.success (descriptor.wrap (.var 0)))).rename ξ =
    LanguageResult.bind (CallableContract.functionType signature.parameterType signature.resultType)
      (SourceCoreFunctions.namedReference signature (ξ position) identity reason)
      (LanguageResult.success (descriptor.wrap (.var 0))) := by
  simp [LanguageResult.bind, LanguageResult.success, LanguageResult.failure, SourceCoreFunctions.namedReference,
    OptionalCell.read, TaggedFunction.identified, SourceCoreCallableContracts.Descriptor.wrap,
    CallableContract.wrap, Expr.rename, Renaming.lift]

/-- A declaration reference without coercions has its instantiation's type. -/
theorem reference_type {source : TypedSource} {context : SourceSemantics.Context} {id : ExpressionId}
    {node : ExpressionNode} {name : String} {instantiation : DeclarationInstantiation}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.declaration instantiation)) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    node.type = instantiation.type ∧ SourceSemantics.DeclarationInstantiation.Admissible context instantiation := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize resultEq : node.type = result at raw
    cases raw with
    | reference referenceValid =>
      cases referenceValid with
      | declaration admissible _ => exact ⟨rfl, admissible⟩

/-- The staged trace of a monomorphic declaration reference without
requirements is the Source's `declaration` rule: the global value, with the
heap unchanged. -/
theorem unchanged {program : Program} {stages : Staging.Recursive.Registry}
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {id : ExpressionId}
    {node : ExpressionNode} {name : String} {instantiation : DeclarationInstantiation} {size : Nat}
    {outcome : Staging.Recursive.Outcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.declaration instantiation))
    (requirements : node.requirements = []) (empty : node.coercions = [])
    (predicates : instantiation.predicates = [])
    (trace : Staging.Recursive.Size.Expression program stages size invocation context environment before id
      outcome after) :
    outcome = .value (.global ⟨instantiation, []⟩) ∧ after = before ∧
      SourceSemantics.DeclarationInstantiation.Valid context instantiation := by
  have same_node : ∀ {other}, ContainsExpression invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have same_occurrence : ∀ {actual requirements}, Staging.Recursive.Occurrence invocation id actual requirements →
      actual = .reference name (.declaration instantiation) := by
    intro actual requirements occurrence
    obtain ⟨other, contains, same, _requirements, _coercions⟩ := occurrence
    cases same_node contains
    exact same.symm.trans form
  cases trace with
  | arrayFault occurrence shape _ | arrayResult occurrence shape _ _ =>
    cases same_occurrence occurrence
    cases shape
  | atomicValue contains _ _ raw =>
    cases same_node contains
    rw [form, requirements] at raw
    cases raw with
    | declaration layout valid closed =>
      cases CompatibleExpressionPrimitives.no_owned layout
      rw [predicates] at closed
      cases closed
      exact ⟨rfl, rfl, valid⟩
  | atomicFault contains _ _ raw =>
    cases same_node contains
    rw [form, requirements] at raw
    cases raw with
    | declarationRequirement layout fault =>
      cases CompatibleExpressionPrimitives.no_owned layout
      cases fault
  | generalizedLocal contains localForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains localForm _ _ _ _ _ _ _ =>
    cases same_node contains
    simp [form] at localForm
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
    exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique found empty
      contains))
  | pair occurrence _ _ | tupleValue occurrence _ _ | constructorValue occurrence _ _
  | unary occurrence _ _ | unaryInvalid occurrence _ _
  | binaryLeftInvalid occurrence _ _ | binaryShortCircuit occurrence _ _
  | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _ | binaryPanic occurrence _ _ _ _
  | notCallable occurrence _ _ | sourceArity occurrence _ _ _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _
  | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _
  | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorFault occurrence _ | constructorMetadataFault occurrence _ | tupleFault occurrence _
  | group occurrence _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unaryOperandFault occurrence _ | binaryLeftFault occurrence _ | binaryRightFault occurrence _ _
  | conditional occurrence _ _ | conditionalFault occurrence _ | calleeFault occurrence _
  | rejected occurrence _ _ | argumentsFault occurrence _ _ _ | applied occurrence _ _ _ _ _ _ =>
    cases same_occurrence occurrence

/-- The global value of a valid monomorphic instantiation has its type. -/
theorem value_typed {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {instantiation : DeclarationInstantiation}
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
    (predicates : instantiation.predicates = []) :
    Dynamic.ValueHasType context heap (.global ⟨instantiation, []⟩) instantiation.type := by
  refine .global valid ⟨fun _ _ looks => (by cases looks), ?_⟩
  intro predicate member
  simp [SourceSemantics.Context.withAssumptions, predicates] at member

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)

include keyPhysical in
/-- The decorated read of an issued header's global cell, through the caller's
slot receipt, yields the positive named handle of the cached closure. -/
theorem named_value {header : Header compiled (Program.ofChecked compiled.sourceProgram)} (member : header ∈ headers)
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD function)
    {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
    (typedStore : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    {canonical actual : Environment} {ξ : Renaming} (agrees : EnvironmentsAgree ξ canonical actual)
    {position : Nat}
    (slot : canonical[position + header.slot]? =
      some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)))
    {signature : SourceCoreCalls.Signature} (sameSignature : header.named.signature = signature)
    {index : Nat} (sameSlot : header.slot = index) {identity reason : Word}
    (number : Word.ofNat? (index + 1) = some identity)
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named signature.key))
    (projected : compiled.compatible.checked.catalog.project header.named.specialized.function.type =
      .ok (CallableContract.functionType signature.parameterType signature.resultType)) :
    ∃ native, Evaluates actual store
        (LanguageResult.bind (CallableContract.functionType signature.parameterType signature.resultType)
          (SourceCoreFunctions.namedReference signature (ξ (position + index)) identity reason)
          (LanguageResult.success (descriptor.wrap (.var 0)))) (.inRight .word native) store ∧
      CallableIndexedOwnedPhysicalNamedAssociation.StaticMember headers keys mapping world
        header.named.specialized.function.type function native
        (CallableContract.functionType signature.parameterType signature.resultType) := by
  subst sameSignature sameSlot
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt prepared aligned member keyPhysical
    physical typedStore
  have cached : compiled.indexed.secondPass.closures[header.slot]? = some
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
        header.code) := by
    rw [aligned.slot, aligned.named, aligned.code]
    exact prepared.cached.trans (congrArg some prepared.compilation.emitted)
  have installed : NamedInstalledCode capture.named :=
    CallableIndexedOwnedFunctionValues.NamedInstalledCode.of_cached capture.named cached capture.embedding_eq
  obtain ⟨_capturedContext, capturedTyped, bodyTyped⟩ :=
    RecursiveGlobalInitializationTyping.stored_closure typedStore capture.read
  exact ⟨_, NamedCalls.native_reference descriptor (agrees slot) capture.read,
    ⟨CallableIndexedOwnedPhysicalNamedAssociation.of_capture owner header capture sourceAt member installed
      identity number projected descriptor (.closure capturedTyped bodyTyped)⟩⟩

variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation (.initial compiled.compatible.checked)
    compiled.indexed.ancestry.graph.inputs.callable.table invocation.source scope id reasonAt lowered)
  (port : Port receipt headers)
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun current => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix current.scope current.canonical) callerProtocol)
  (cache : ∀ {current}, callerProtocol.State current →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled current.mapping current.store)
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (included : NamedValuesIncluded headers keys functions)
  {bodyRelation : ActualBodyInvocation.BodyRelation} {index : ActualBodyInvocation.Index compiled bodyRelation}
  {registry : Staging.Recursive.Registry} (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions

include owner keyPhysical receipt port callerBridge cache included in
/-- The emitted code runs to the positive named handle of the selected header
without changing the store, and the payload relation's function case relates
it to the Source's global value. -/
theorem value_run {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
    {canonical actual : Environment} {ξ : Renaming}
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (nodeType : receipt.node.type = receipt.instantiation.type) :
    ∃ native, Evaluates actual store (lowered.expression.rename ξ) (.inRight .word native) store ∧
      (model).Represents mapping world receipt.node.type (.global ⟨receipt.instantiation, []⟩) native
        lowered.type := by
  have sourceType : receipt.node.type = port.header.named.specialized.function.type :=
    nodeType.trans port.instantiation_type
  have projected : compiled.compatible.checked.catalog.project port.header.named.specialized.function.type =
      .ok (CallableContract.functionType receipt.signature.parameterType receipt.signature.resultType) := by
    rw [← sourceType, ← receipt.nativeType]
    exact receipt.metadata.projected
  obtain ⟨native, evaluated, member⟩ := named_value owner keyPhysical port.member port.prepared port.aligned
    port.sourceAt (cache initial) heaps.runtime_hasTypes agrees (callerBridge.slots initial port.header port.member)
    port.signature port.slot (reason := compilation.internalReason) receipt.number receipt.descriptor projected
  have shape : port.header.named.specialized.function.type = .function receipt.parameter receipt.result := by
    rw [port.specialized]
    exact receipt.shape
  refine ⟨native, ?_, ?_⟩
  · rw [receipt.emitted, emitted_rename]
    exact evaluated
  · rw [sourceType, receipt.nativeType, port.global_eq, shape]
    rw [shape] at member
    exact .function (included member)

include owner keyPhysical receipt port callerBridge cache included unique in
/-- A named function value at an accepted site preserves its staged
execution: the Source's `declaration` rule is the only staged trace, and the
emitted read of the header's global cell represents its value. -/
theorem preserves (size : Nat) :
    CellAwareInvocationExpressionBounds.PreservesAt (attachment := attachment) callerBridge.forgetSlots context
      model index registry invocation (Point scope id lowered) faults size := by
  intro current child code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨rfl, rfl, valid⟩ := unchanged unique receipt.metadata.found receipt.form receipt.metadata.requirements
    receipt.metadata.coercions receipt.monomorphic.predicates trace
  obtain ⟨nodeType, _admissible⟩ := reference_type unique receipt.metadata.found receipt.form
    receipt.metadata.coercions typed
  obtain ⟨native, evaluated, related⟩ := value_run owner keyPhysical receipt port callerBridge cache functions
    included initial heaps agrees nodeType
  refine ⟨.inRight .word native, store, mapping, world, evaluated, .value related, heaps, .refl _, .refl _,
    .refl _ _, .refl _, .refl _ _ _ _, initial, callerProtocol.refl initial, ?_⟩
  exact ⟨admitted.rows, by
    intro value same
    cases same
    exact ⟨nodeType ▸ value_typed valid receipt.monomorphic.predicates, admitted.heap⟩⟩

include owner keyPhysical receipt port callerBridge cache included unique in
/-- Native completion of a named function value at an accepted site
reconstructs the Source's `declaration` rule as the staged atomic value. -/
theorem reflects
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
    (size : Nat) :
    CellAwareInvocationExpressionBounds.ReflectsAt (attachment := attachment) callerBridge.forgetSlots context
      model index registry invocation (Point scope id lowered) faults size := by
  intro current child code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨nodeType, admissible⟩ := reference_type unique receipt.metadata.found receipt.form
    receipt.metadata.coercions typed
  have valid := CompatibleSourceInstantiationClosure.declaration_valid admissible runtime.variables_closed
    (receipt.monomorphic.ordinary compilation.plan).ranges
  obtain ⟨native, evaluated, related⟩ := value_run owner keyPhysical receipt port callerBridge cache functions
    included initial heaps agrees nodeType
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated completed.sound
  refine ⟨Staging.Recursive.Size.stepSize [], .value (.global ⟨receipt.instantiation, []⟩), before, mapping,
    world, .atomicValue (lookupExpression?_sound receipt.metadata.found) (receipt.form.symm ▸ .reference _ _)
      receipt.metadata.coercions ?rule, .value related, heaps, .refl _, .refl _, .refl _ _, .refl _,
    .refl _ _ _ _, initial, callerProtocol.refl initial, ?post⟩
  case rule =>
    rw [receipt.form, receipt.metadata.requirements]
    exact .declaration (owned := []) (produced := []) rfl valid
      (by rw [receipt.monomorphic.predicates]; exact .nil)
  case post =>
    exact ⟨admitted.rows, by
      intro value same
      cases same
      exact ⟨nodeType ▸ value_typed valid receipt.monomorphic.predicates, admitted.heap⟩⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationNamedValueBounds
end

section
/-! The lifting of a value site's original Source executions: the Source's
`declaration` rule is an atomic form, so the staged atomic value and fault
rules carry it unchanged, as for a builtin value in `nested_value` and
`nested_fault`. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedValueLifting
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared)
open CellAwareInvocationAcceptedValueSites (ValueSite)

variable {program : Program} {registry : Staging.Recursive.Registry}
  {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {scope : Staging.Recursive.Scope} {id : ExpressionId}

/-- A sized value execution of a value site is the staged atomic value. -/
theorem value_lift (unique : NodeOccurrencesUnique scope.source) (site : ValueSite prepared named scope.source id)
    {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {value : Dynamic.Value}
    (trace : SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment
      before id value after) :
    Staging.Recursive.Expression program registry scope context environment before id (.value value) after :=
  Staging.Recursive.Lifting.atomic_nonlocal unique (lookupExpression?_sound site.found)
    (by rw [site.form]; exact .reference _ _) site.coercions
    (fun name binder same => by rw [site.form] at same; cases same) (.value trace.sound)

/-- A sized fault execution of a value site is the staged atomic fault. -/
theorem value_lift_fault (unique : NodeOccurrencesUnique scope.source)
    (site : ValueSite prepared named scope.source id)
    {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.ExpressionFaults program size context scope.evidence scope.source environment
      before id reason after) :
    Staging.Recursive.Expression program registry scope context environment before id
      (.fault (.semantic reason)) after :=
  Staging.Recursive.Lifting.atomic_nonlocal unique (lookupExpression?_sound site.found)
    (by rw [site.form]; exact .reference _ _) site.coercions
    (fun name binder same => by rw [site.form] at same; cases same) (.fault trace.sound)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedValueLifting
end

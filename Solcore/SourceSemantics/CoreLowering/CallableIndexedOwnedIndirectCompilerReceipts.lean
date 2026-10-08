import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceAdapters
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArgumentReceipts

/-! One accepted indirect compiler call retains its literal named factory,
ordered physical children, prepared callsite and independent raw Source typing.
The actual contextual policy is selected by its original outer bind. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectCompilerReceipts
open Core Frontend SourceInference
open CallableIndexedNamedGeneration

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The static factory keeps the complete solved row and the exact certificate
family at this Source, scope and administrative context. -/
structure Factory
    (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) (namedCode : Expr)
    (compilation : Compilation compiled.indexed caller.named diagnostics namedCode)
    (source : TypedSource) (sourceContext : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (scope : SourceCoreLocalCell.Scope)
    (administrative : Core.Context)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate) : Prop where
  sourceView : LambdaMetadataViews.MetadataView (CallableIndexedNamedGeneration.source caller.named) source
  namedLedger : (context compiled.indexed caller.named).solvedRequirements = caller.solved
  sourceLedger : sourceContext.solvedRequirements = (context compiled.indexed caller.named).solvedRequirements
  valid : CompatibleRuntimeContextValidity.Valid caller.solved sourceContext evidence

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Only the parent read prefix is inverted here. The existing indirect receipt
owns the full indirect lowering branch and its ordered compiler calls. -/
private theorem accepted_read
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution} {original : ExpressionNode} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some original)
    (form : original.form = .call callee ids (.indirect metadata))
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    ∃ node type, policy.readExpression source id = .ok (node, type) := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owned : id.occurrence.owner = source.owner
  · simp only [owned, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind,
      pure, Except.pure] at accepted
    have bypass := special (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) compilation
        childSource childScope childId childReasonAt) (fuel + 1)
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals simp only [form, bind, Except.bind, pure, Except.pure] at accepted
    all_goals
      obtain ⟨pair, read, _⟩ := bind_ok accepted
      exact ⟨pair.1, pair.2, read⟩
  · simp [owned, bind, Except.bind] at accepted

private theorem row_length {source : TypedSource} {context : SourceSemantics.Context}
    {ids : List ExpressionId} {types : List TypeSystem.Ty}
    (typed : ExpressionsHaveTypes source context ids types) : ids.length = types.length := by
  induction ids generalizing types with
  | nil => cases typed; rfl
  | cons head tail ih =>
    cases typed with
    | cons _ rest => exact congrArg Nat.succ (ih rest)

private theorem row_member {source : TypedSource} {context : SourceSemantics.Context}
    {ids : List ExpressionId} {types : List TypeSystem.Ty}
    (typed : ExpressionsHaveTypes source context ids types) {id : ExpressionId} (member : id ∈ ids) :
    ∃ type, ExpressionHasType source context id type := by
  induction ids generalizing types with
  | nil => cases member
  | cons head tail ih =>
    cases typed with
    | cons headTyped tailTyped =>
      rcases List.mem_cons.mp member with same | remaining
      · subst id; exact ⟨_, headTyped⟩
      · exact ih tailTyped remaining

private theorem zip_positions {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
    (length : ids.length = codes.length) : (ids.zip codes).map Prod.fst = ids := by
  induction ids generalizing codes with
  | nil => simp
  | cons head tail ih =>
    cases codes with
    | nil => simp at length
    | cons code rest =>
      simp only [List.length_cons, Nat.succ.injEq] at length
      simp only [List.zip_cons_cons, List.map_cons, ih length]

section Leaf
variable
    {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
    {source : TypedSource} {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (factory : Factory caller diagnostics namedCode compilation source sourceContext evidence scope administrative certificates)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)

/-- Compiler and raw Source function components stay distinct until a genuine
callee compatible-read equation identifies them. -/
structure Receipt (factory : Factory caller diagnostics namedCode compilation source sourceContext evidence scope administrative certificates) where
  compiler : CallableIndirectCallCertificates.Receipt policy body fuel
    (context compiled.indexed caller.named) source scope id callee ids metadata reasonAt lowered
  callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active
  prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native
  sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler
  parentMetadata : CompatibleExpressionReads.Metadata compiled.compatible.checked source id compiler.original compiler.type
  sourceParameter : TypeSystem.Ty
  sourceResult : TypeSystem.Ty
  sourceTypes : List TypeSystem.Ty
  calleeTyped : ExpressionHasType source sourceContext callee (.function sourceParameter sourceResult)
  argumentsTyped : ExpressionsHaveTypes source sourceContext ids sourceTypes
  application : IndirectApplicationValid sourceContext metadata sourceTypes sourceParameter
  sourceBundle : TypeSystem.Ty.productMany sourceTypes = sourceParameter
  positions : compiler.entries.map Prod.fst = callee :: ids
  physicalCount : ids.length = compiler.codes.length
  generated : ∀ child code, (child, code) ∈ compiler.entries →
    ∃ node, source.lookupExpression? child = some node ∧
      ExpressionHasType source sourceContext child node.type ∧
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
        (context compiled.indexed caller.named) source scope child reasonAt = .ok code

/-- Actual accepted lowering selects one receipt; all other fields are finite
static projections at that same invocation and factory. -/
theorem Receipt.of_functions {original : ExpressionNode}
    (found : source.lookupExpression? id = some original)
    (form : original.form = .call callee ids (.indirect metadata))
    (typed : ExpressionHasType source sourceContext id original.type)
    (unique : NodeOccurrencesUnique source)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower (context compiled.indexed caller.named) child budget source scope id reasonAt) = .ok none)
    (parentRead : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked source id)
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      (context compiled.indexed caller.named) source scope id reasonAt = .ok lowered) :
    Nonempty (Receipt native active factory (policy := policy) (body := body) (fuel := fuel)
      (id := id) (callee := callee) (ids := ids) (metadata := metadata) (reasonAt := reasonAt) (lowered := lowered)) := by
  obtain ⟨node, type, read⟩ := accepted_read found form special accepted
  have actualMetadata := CompatibleExpressionReads.metadata_of_read (parentRead ▸ read)
  have nodeEq := Option.some.inj (actualMetadata.found.symm.trans found)
  subst node
  obtain ⟨compiler⟩ := CallableIndirectCallCertificates.of_functions found form special read form accepted
  have actualNode := Option.some.inj ((CompatibleExpressionReads.metadata_of_read (parentRead ▸ compiler.read)).found.symm.trans compiler.found)
  have parentMetadata : CompatibleExpressionReads.Metadata compiled.compatible.checked source id compiler.original compiler.type := by
    exact actualNode ▸ CompatibleExpressionReads.metadata_of_read (parentRead ▸ compiler.read)
  have nodeMetadata := CompatibleExpressionReads.metadata_of_read (parentRead ▸ compiler.read)
  have nodeId : compiler.node.id = id := (lookupExpression?_sound nodeMetadata.found).2
  obtain ⟨prepared⟩ := CallableIndexedOwnedIndirectSourceAdapters.Prepared.of_receipt compiler native active callables nodeId
  obtain ⟨parameter, result, types, calleeTyped, argumentsTyped, application⟩ :=
    CallableIndexedOwnedStoredClosureArgumentReceipts.original_facts unique found form typed
  have arity : ids.length = metadata.argumentCount := by
    cases application with
    | intro count _ _ _ => exact (row_length argumentsTyped).trans count.symm
  have sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler :=
    ⟨parentMetadata.requirements, parentMetadata.coercions, arity⟩
  obtain ⟨physicalCount, children⟩ := compiler.ordered_children
  have positions : compiler.entries.map Prod.fst = callee :: ids := by
    simp only [CallableIndirectCallCertificates.Receipt.entries, List.map_cons, zip_positions physicalCount]
  have generated : ∀ child code, (child, code) ∈ compiler.entries →
      ∃ node, source.lookupExpression? child = some node ∧ ExpressionHasType source sourceContext child node.type ∧
        SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
          (context compiled.indexed caller.named) source scope child reasonAt = .ok code := by
    intro child code member
    have childTyped : ∃ type, ExpressionHasType source sourceContext child type := by
      rcases List.mem_cons.mp member with same | remaining
      · cases same; exact ⟨_, calleeTyped⟩
      · exact row_member argumentsTyped (List.of_mem_zip remaining).1
    obtain ⟨childType, typing⟩ := childTyped
    obtain ⟨node, contains, stored⟩ := typing.stored_type
    exact ⟨node, lookupExpression?_complete unique contains, (by rw [stored]; exact typing), children child code member⟩
  exact ⟨⟨compiler, callables, prepared, sourceParent, parentMetadata, parameter, result, types,
    calleeTyped, argumentsTyped, application,
    CallableIndexedOwnedStoredClosureArgumentReceipts.empty_bundle application compiler.argumentCoercions,
    positions, physicalCount, generated⟩⟩

/-- The actual callable profile supplies the native function convention. -/
theorem Receipt.actualFunctionType
    (receipt : Receipt native active factory (policy := policy) (body := body) (fuel := fuel)
      (id := id) (callee := callee) (ids := ids) (metadata := metadata) (reasonAt := reasonAt) (lowered := lowered)) :
    policy.callables.functionType = CallableContract.functionType := by
  rw [receipt.callables]
  rfl

/-- A pointwise compatible callee read identifies raw components through the
same Source lookup. No native type projection is inverted. -/
theorem Receipt.callee_source_type
    (receipt : Receipt native active factory (policy := policy) (body := body) (fuel := fuel)
      (id := id) (callee := callee) (ids := ids) (metadata := metadata) (reasonAt := reasonAt) (lowered := lowered))
    (unique : NodeOccurrencesUnique source)
    (calleeRead : policy.readExpression source callee =
      SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked source callee) :
    receipt.compiler.parameter = receipt.sourceParameter ∧ receipt.compiler.result = receipt.sourceResult := by
  have actual := CompatibleExpressionReads.metadata_of_read (calleeRead ▸ receipt.compiler.calleeRead)
  obtain ⟨node, contains, stored⟩ := receipt.calleeTyped.stored_type
  have same := Option.some.inj (actual.found.symm.trans (lookupExpression?_complete unique contains))
  have raw : receipt.compiler.calleeNode.type = .function receipt.sourceParameter receipt.sourceResult := by
    rw [same]; exact stored
  have typeEq := receipt.compiler.calleeType.symm.trans raw
  exact TypeSystem.Ty.function.inj typeEq
end Leaf


abbrev SpecialLowerer := SourceCoreFunctions.Context → SourceCoreFunctions.ExpressionLowerer → Nat →
  TypedSource → SourceCoreLocalCell.Scope → ExpressionId → (ExpressionId → Word) →
  Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr)

/-- The original contextual bind chooses these literal policy fields. The
special callback is retained as the exact value inside the selected policy. -/
structure ContextualPolicyReceipt (named : Named)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) (namedCode : Expr)
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (fuel : Nat) (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr) where
  policy : SourceCoreFunctions.Policy
  lowerBody : SourceCoreFunctions.BodyLowerer
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
    (context compiled.indexed named) source scope id reasonAt = .ok lowered
  callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext []
  readExpression : policy.readExpression = fun source id => do
    let viewed ← SourceCoreGeneralFunctions.contextualSource compiled.indexed.base.sourceProgram
      (context compiled.indexed named).plan compiled.indexed.base.locals (context compiled.indexed named).owner none source id
    ((representation compiled.indexed).atContext named.signature.key []).expressions.readExpression viewed id
  specialLowerer : SpecialLowerer
  special_eq : policy.lowerSpecial? = some specialLowerer
  special_body : specialLowerer = fun current child budget source scope id reasonAt => do
    let source ← SourceCoreGeneralFunctions.contextualSource compiled.indexed.base.sourceProgram
      current.plan compiled.indexed.base.locals current.owner none source id
    let node ← match source.lookupExpression? id with
      | some node => pure node
      | none => throw (.missingExpression id)
    let onLocalError := fun (error : SourceCoreLocalPolymorphism.Error) => match error with
      | .metadata error => error
      | _ => SourceCoreBasic.Error.unsupportedExpression id node.form
    let initialized := compiled.indexed.base.locals.bindings.find? fun binding =>
      decide (binding.caller = current.owner ∧ binding.initializer = id)
    if let some initialized := initialized.filter (fun _ => (none : Option ExpressionId) ≠ some id) then
      let binding ← (compiled.indexed.base.locals.binding current.owner initialized.binder.id).mapError onLocalError
      let lowered ← (SourceCoreLocalPolymorphism.lowerInitializer binding [] fun candidate => do
        let emission ← (SourceCoreLocalEvidence.prepareForEmission compiled.indexed.base.sourceProgram current.plan
          candidate none compilation.parents).mapError fun _ =>
            SourceCoreLocalPolymorphism.Error.initializerMetadataMismatch id
        let prepared := emission.prepared
        let childContext := { current with solvedRequirements := prepared.caller.function.solvedRequirements }
        let lowered ← (SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
          ((representation compiled.indexed).atContext named.signature.key []) compiled.indexed.base.sourceProgram.signatures
          compiled.indexed.base.locals compilation.parents compilation.own.assignments diagnostics childContext
          compiled.indexed.base.callableContext (some prepared) (some id) (min budget fuel) prepared.source scope id reasonAt)
          |>.mapError SourceCoreLocalPolymorphism.Error.metadata
        (SourceCoreBasic.ensureType (.occurrence id.occurrence) candidate.type lowered.type)
          |>.mapError SourceCoreLocalPolymorphism.Error.metadata
        match lowered.expression with
        | .inRight .word closure => pure closure
        | _ => throw (.initializerMetadataMismatch id)).mapError onLocalError
      return some lowered
    let evidence ← SourceCoreEvidence.lowerWithProjector compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []).expressions.projectType
      named.specialized current child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext [])
    if let some lowered := evidence then return some lowered
    match node.form with
    | .reference _ (.local binder) =>
      if compiled.indexed.base.locals.bindings.any (fun binding =>
          decide (binding.caller = current.owner ∧ binding.binder.id = binder)) then
        let lowered ← (SourceCoreLocalPolymorphism.lowerRead compiled.indexed.base.locals current.owner []
          source scope id (reasonAt id)) |>.mapError onLocalError
        let viewed ← ((representation compiled.indexed).atContext named.signature.key []).localReadView
          current.owner [] source scope id lowered
        SourceCoreBasic.ensureType (.occurrence id.occurrence) lowered.type viewed.type
        return some viewed
      else return none
    | _ => return none
  binder : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
    ((representation compiled.indexed).atContext named.signature.key []) compiled.indexed.base.locals named.signature.key []
  recipe : lowerBody = SourceCoreGeneralFunctions.bodyLowererWithRepresentation
    ((representation compiled.indexed).atContext named.signature.key [])
    (context compiled.indexed named).solvedRequirements compilation.own.assignments diagnostics
    (context compiled.indexed named).owner
    (SourceCoreGeneralFunctions.contextualBinder
      ((representation compiled.indexed).atContext named.signature.key []) compiled.indexed.base.locals named.signature.key [])

/-- The outer contextual bind is eliminated once. Its recursive callback and
minimum budget remain in the original selected special lowerer. -/
theorem ContextualPolicyReceipt.of_accepted
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []) compiled.indexed.base.sourceProgram.signatures
      compiled.indexed.base.locals compilation.parents compilation.own.assignments diagnostics (context compiled.indexed named)
      compiled.indexed.base.callableContext none none (fuel + 1) source scope id reasonAt = .ok lowered) :
    Nonempty (ContextualPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation fuel source scope id reasonAt lowered) := by
  rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
  dsimp only at accepted
  change (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key |>.mapError SourceCoreBasic.Error.callPreparation) >>= _ = .ok lowered at accepted
  rw [record] at accepted
  simp only [Except.mapError, bind, Except.bind] at accepted
  exact ⟨⟨_, _, accepted, rfl, rfl, _, rfl, rfl, rfl, rfl⟩⟩

/-- Only pointwise Source read agreement and actual special delegation are
required from the selected policy. Neither field is a completed compiler leaf. -/
structure PolicyFor
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed named diagnostics namedCode}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (selected : ContextualPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation fuel source scope id reasonAt lowered) : Prop where
  parentRead : selected.policy.readExpression source id =
    SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked source id
  special : ∀ child budget, (match selected.policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower (context compiled.indexed named) child budget source scope id reasonAt) = .ok none

section ContextualLeaf
variable
    {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
    {source : TypedSource} {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (factory : Factory caller diagnostics namedCode compilation source sourceContext evidence scope administrative certificates)
    (native : SourceCoreGeneralFunctions.CallableContext)
    {fuel : Nat} {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

/-- The selected policy and indirect leaf share the literal input Compilation,
Source, scope, administrative context and complete solved factory row. -/
structure ContextualReceipt where
  nativeContext : compiled.indexed.base.callableContext = some native
  selected : ContextualPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation fuel source scope id reasonAt lowered
  agreements : PolicyFor selected
  receipt : Receipt native [] factory (policy := selected.policy) (body := selected.lowerBody)
    (fuel := fuel) (id := id) (callee := callee) (ids := ids) (metadata := metadata)
    (reasonAt := reasonAt) (lowered := lowered)

/-- Contextual acceptance selects the actual policy once, then the finite
indirect port builds all compiler, Prepared and raw Source fields internally. -/
theorem ContextualReceipt.of_accepted
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan caller.named.signature.key = .ok caller.named.specialized)
    (nativeContext : compiled.indexed.base.callableContext = some native)
    {original : ExpressionNode}
    (found : source.lookupExpression? id = some original)
    (form : original.form = .call callee ids (.indirect metadata))
    (typed : ExpressionHasType source sourceContext id original.type)
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext caller.named.signature.key []) compiled.indexed.base.sourceProgram.signatures
      compiled.indexed.base.locals compilation.parents compilation.own.assignments diagnostics (context compiled.indexed caller.named)
      compiled.indexed.base.callableContext none none (fuel + 1) source scope id reasonAt = .ok lowered)
    (agreements : ∀ selected : ContextualPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
      fuel source scope id reasonAt lowered, PolicyFor selected) :
    Nonempty (ContextualReceipt factory native (fuel := fuel) (id := id) (callee := callee) (ids := ids)
      (metadata := metadata) (reasonAt := reasonAt) (lowered := lowered)) := by
  obtain ⟨selected⟩ := ContextualPolicyReceipt.of_accepted compilation record accepted
  have pointwise := agreements selected
  have callables : selected.policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) [] := by
    rw [selected.callables, nativeContext]
  obtain ⟨receipt⟩ := Receipt.of_functions factory native [] found form typed unique
    pointwise.special pointwise.parentRead callables selected.accepted
  exact ⟨⟨nativeContext, selected, pointwise, receipt⟩⟩
end ContextualLeaf

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectCompilerReceipts

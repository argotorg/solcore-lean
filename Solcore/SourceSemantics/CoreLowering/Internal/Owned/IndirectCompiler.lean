import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures
import Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionCallsHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NestedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReadyFamilies

/-!
# Owned callables: indirect compiler receipts

Compiler receipts and policy inputs of indirect calls, and selected indirect heads and bodies.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectCompilerReceipts
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectCompilerPolicyInputs
/-! The selected contextual callback delegates an ordinary indirect node using
its actual Source and metadata. Exact initializer absence and empty argument
coercions remain genuine static inputs at this occurrence. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectCompilerPolicyInputs
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedOwnedIndirectCompilerReceipts

/-- Contextual local normalization leaves the actual indirect Source intact. -/
theorem contextualSource_indirect
    (program : CheckedProgram) (plan : SourceCompilationPlan.Plan)
    (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceSpecialization.SpecializationKey)
    (parent : Option SourceCoreLocalEvidence.Prepared)
    {source : TypedSource} {id callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect metadata)) :
    SourceCoreGeneralFunctions.contextualSource program plan locals owner parent source id = .ok source := by
  simp [SourceCoreGeneralFunctions.contextualSource, found, form]

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Allocator and lambda hooks preserve the original compatible read field. -/
theorem representation_read (named : Named) :
    ((representation compiled.indexed).atContext named.signature.key []).expressions.readExpression =
      SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked := by
  rfl

/-- The original evidence gate returns none at this exact metadata, before
performing owner or authenticated declaration checks. -/
theorem evidence_none_indirect
    (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (context : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    {source : TypedSource} (scope : SourceCoreLocalCell.Scope)
    {id callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution} {node : ExpressionNode}
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (arguments : metadata.argumentCoercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller context child budget source scope id reasonAt callables = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    rfl
  simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions, arguments]

section Policy
variable
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed named diagnostics namedCode}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {node : ExpressionNode}

/-- Both policy agreements follow from the same selected callback and genuine
pointwise metadata, without first constructing an indirect compiler receipt. -/
theorem policy_of_indirect_metadata
    (selected : ContextualPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
      fuel source scope id reasonAt lowered)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (arguments : metadata.argumentCoercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) = none) :
    PolicyFor selected := by
  have sameSource := contextualSource_indirect compiled.indexed.base.sourceProgram
    (context compiled.indexed named).plan compiled.indexed.base.locals
    (context compiled.indexed named).owner none found form
  constructor
  · rw [selected.readExpression]
    simp only [sameSource, bind, Except.bind]
    rw [representation_read]
  · intro child budget
    rw [selected.special_eq, selected.special_body]
    have noEvidence := evidence_none_indirect compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []).expressions.projectType
      named.specialized (context compiled.indexed named) child budget scope reasonAt
      (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext [])
      found form requirements coercions arguments
    simp only [sameSource, bind, Except.bind, found, pure, Except.pure, ordinary,
      Option.filter_none, noEvidence, form]

end Policy

section Contextual
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
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}

/-- The accepted contextual compiler chooses its actual policy once. Its read
and delegation inputs are derived internally from the same Source occurrence. -/
theorem contextual_receipt_of_indirect_metadata
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan caller.named.signature.key = .ok caller.named.specialized)
    (nativeContext : compiled.indexed.base.callableContext = some native)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (arguments : metadata.argumentCoercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed caller.named).owner ∧ binding.initializer = id)) = none)
    (typed : ExpressionHasType source sourceContext id node.type)
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext caller.named.signature.key []) compiled.indexed.base.sourceProgram.signatures
      compiled.indexed.base.locals compilation.parents compilation.own.assignments diagnostics (context compiled.indexed caller.named)
      compiled.indexed.base.callableContext none none (fuel + 1) source scope id reasonAt = .ok lowered) :
    Nonempty (ContextualReceipt factory native (fuel := fuel) (id := id) (callee := callee) (ids := ids)
      (metadata := metadata) (reasonAt := reasonAt) (lowered := lowered)) := by
  exact ContextualReceipt.of_accepted factory native record nativeContext found form typed unique accepted
    (fun selected => policy_of_indirect_metadata selected found form requirements coercions arguments ordinary)

end Contextual
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectCompilerPolicyInputs
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedIndirectHeads
/-! Selected indirect heads retain the original callsite and a genuine lambda
callee occurrence. Selection contains static code, ordered binders and parsed
guards; it stores no child or body execution law. Body continuations are supplied
only at the real ordered-argument post, for use by the shared mutual closer. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedIndirectHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedIndirectExpressionHeads CallableIndexedOwnedIndirectSourceAdapters
open RecursiveNamedCatalogInvocationBounds (Below)
universe u

/-- An authentic original lambda occurrence, including its empty raw coercion
path. The policy-read compiler node remains a separate receipt. -/
structure LambdaCallee (source : TypedSource) (id : ExpressionId) where
  node : ExpressionNode
  found : source.lookupExpression? id = some node
  parameters : List TypedBinder
  result : TypeSystem.Ty
  body : List StatementId
  form : node.form = .lambda parameters result body
  coercions : node.coercions = []

def LambdaCallee.function {source : TypedSource} {id : ExpressionId}
    (callee : LambdaCallee source id) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment) : Dynamic.Closure :=
  ⟨callee.parameters, callee.result, callee.body, source, environment, context, evidence⟩

/-- Direct case inversion retains the actual formation environment: the
closure captures the copies of its captured cells, made in the reached heap. -/
theorem LambdaCallee.source_value {source : TypedSource} {id : ExpressionId}
    (callee : LambdaCallee source id) (unique : NodeOccurrencesUnique source)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}
    (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    ∃ captured, value = .closure (callee.function context evidence captured) ∧
      Dynamic.EnvironmentCopies source environment before captured after := by
  have contains := lookupExpression?_sound callee.found
  cases evaluated with
  | intro found raw coercions =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans callee.found)
    subst same
    rw [callee.coercions] at coercions
    cases coercions
    rw [callee.form] at raw
    cases raw with
    | lambda _ snapshot => exact ⟨_, rfl, snapshot⟩
  | generalizedLocal found form _ _ _ _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans callee.found)
    subst same
    rw [callee.form] at form
    cases form

/-- The original lambda form and empty coercions exclude every callee fault. -/
theorem LambdaCallee.excludes_fault {source : TypedSource} {id : ExpressionId}
    (callee : LambdaCallee source id) (unique : NodeOccurrencesUnique source)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (failed : Dynamic.ExpressionFaults program context evidence source environment before id reason after) : False := by
  have contains := lookupExpression?_sound callee.found
  cases failed with
  | missing absent => exact Dynamic.ExpressionAbsentIn.excludes_contains absent contains
  | form found raw =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans callee.found)
    subst same
    rw [callee.form] at raw
    cases raw
  | coercion found _ failed =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans callee.found)
    subst same
    rw [callee.coercions] at failed
    cases failed
  | generalizedLocalRequirement found form _ _ _ _ _ _ _ | generalizedLocalCoercion found form _ _ _ _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans callee.found)
    subst same
    rw [callee.form] at form
    cases form

/-- The original sized indirect rule supplies only successful lambda callees
and its genuine argument/application suffix. Arity and coercion faults are
excluded by the authentic empty-path parent receipt. -/
theorem suffix_of_source
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {node : ExpressionNode} {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect metadata)) (coercions : node.coercions = [])
    (argumentCoercions : metadata.argumentCoercions = []) (arity : ids.length = metadata.argumentCount)
    (lambda : LambdaCallee source callee) (unique : NodeOccurrencesUnique source)
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    {types : List TypeSystem.Ty} (sourceArguments : ExpressionsHaveTypes source context ids types)
    (sourceCount : types.length = metadata.argumentCount)
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    ∃ calleeSize argumentsSize callSize captured calleeHeap,
      SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee
        (.closure (lambda.function context evidence captured)) calleeHeap ∧
      Dynamic.EnvironmentCopies source environment before captured calleeHeap ∧
      SourceSuffix program context evidence source environment calleeHeap ids (lambda.function context evidence captured)
        argumentsSize callSize outcome after ∧ calleeSize < size ∧ argumentsSize < size ∧ callSize ≤ size := by
  have independent := CallableIndirectCallSourceBounds.indirect_inv_sized found form coercions unique trace
  cases independent with
  | calleeFault child smaller => exact False.elim (lambda.excludes_fault unique child.sound)
  | notCallable child invalid smaller =>
    obtain ⟨_, same, _⟩ := lambda.source_value unique child.sound
    rw [same] at invalid
    exact False.elim (invalid trivial)
  | argumentsFault first callable children firstSmall childrenSmall =>
    obtain ⟨captured, same, copy⟩ := lambda.source_value unique first.sound
    cases same
    exact ⟨_, _, 0, captured, _, first, copy, .argumentFault children, firstSmall, childrenSmall, Nat.zero_le _⟩
  | sourceArity first children mismatch firstSmall childrenSmall => exact False.elim (mismatch arity.symm)
  | argumentCoercionFault first children sameArity pack failed firstSmall childrenSmall coercionSmall =>
    rw [argumentCoercions] at failed
    cases failed
  | applied layout first children packed converted unpacked sameArity appliedArity called firstSmall childrenSmall coercionSmall callSmall =>
    obtain ⟨captured, same, copy⟩ := lambda.source_value unique first.sound
    cases same
    rw [argumentCoercions] at converted
    cases converted
    have sameArguments := Dynamic.ValuesPack.injective_of_length_eq packed unpacked
      ((arguments_count_of_source_admission wellFormed runtime covers (locals.mono copy.metadata_extends)
        (heapTyped.copy copy) sourceArguments sourceCount children).trans appliedArity.symm)
    cases sameArguments
    exact ⟨_, _, _, captured, _, first, copy, SourceSuffix.of_call children (.value called), firstSmall, childrenSmall,
      Nat.le_of_lt callSmall⟩
  | applicationFault first children packed converted unpacked sameArity appliedArity called firstSmall childrenSmall coercionSmall callSmall =>
    obtain ⟨captured, same, copy⟩ := lambda.source_value unique first.sound
    cases same
    rw [argumentCoercions] at converted
    cases converted
    have sameArguments := Dynamic.ValuesPack.injective_of_length_eq packed unpacked
      ((arguments_count_of_source_admission wellFormed runtime covers (locals.mono copy.metadata_extends)
        (heapTyped.copy copy) sourceArguments sourceCount children).trans appliedArity.symm)
    cases sameArguments
    exact ⟨_, _, _, captured, _, first, copy, SourceSuffix.of_call children (.fault called), firstSmall, childrenSmall,
      Nat.le_of_lt callSmall⟩



open CallableIndexedLambdaNestedRuntimeBodyMeaning
open CallableIndexedOwnedLambdaFormationReceipts (FormedRecord of_formation formation_exists)
section Certificates
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

/-- Pure obligations on the exact original formation Code. Ordered argument
certificates retain duplicates, and both parsed decisions use its descriptor. -/
structure Selection
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
    {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
    {function : Dynamic.Closure} {calleeScope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed function calleeScope administrative) : Prop where
  children : DataExpressionSequence.Tree source certificate scope ids
    (code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) compiler.codes
  nativeTypes : compiler.codes.map (·.type) = code.receipt.loweredParameters.map Prod.snd
  escaped : faults .controlEscapedFunction code.compilation.internalReason
  rawResult : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType function.resultType
  nativeResult : compiler.resultType = code.receipt.resultCore
  stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown code.descriptor.id = none
  arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown code.descriptor.id = none

/-- The original callsite and authentic literal producer remain complete.
Selection checks that producer's Code, not every generic ValueRep witness. -/
structure Receipt (caller : CallableIndexedOwnedFunctionValues.Header compiled program)
    (certificate : GenericExpressionMeaning.Certificate)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  policy : SourceCoreFunctions.Policy
  body : SourceCoreFunctions.BodyLowerer
  fuel : Nat
  compilation : SourceCoreFunctions.Context
  callee : ExpressionId
  ids : List ExpressionId
  metadata : IndirectCallResolution
  reasonAt : ExpressionId → Word
  compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered
  native : SourceCoreGeneralFunctions.CallableContext
  prepared : Prepared compiler native
  parent : SourceParent compiler
  rank : Nat
  formation : LambdaAt (values := .initial compiled.compatible.checked) headers caller registry faults rank
    source context evidence scope callee compiler.calleeCode
  sameSource : source = CallableIndexedNamedGeneration.source caller.named
  calleeCertified : certificate scope callee compiler.calleeCode
  sourceTyped : ExpressionHasType source context callee (.function compiler.parameter compiler.result)
  sourceTypes : List TypeSystem.Ty
  sourceArguments : ExpressionsHaveTypes source context ids sourceTypes
  sourceCount : sourceTypes.length = metadata.argumentCount
  selected : ∀ environment, Selection (faults := faults) (certificate := certificate) compiler prepared (actualCode formation environment)

/-- The same authentic node creates the raw Source formation packet. -/
def Receipt.lambda {caller : CallableIndexedOwnedFunctionValues.Header compiled program}
    (head : Receipt (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) caller certificate scope id lowered) :
    LambdaCallee source head.callee where
  node := head.formation.code.sourceNode
  found := head.formation.found
  parameters := head.formation.parameters
  result := head.formation.result
  body := head.formation.statements
  form := head.formation.code.sourceForm
  coercions := head.formation.coercions

/-- Original source/dictionary/captured locations are exactly the formed ones. -/
theorem Receipt.function_eq {caller : CallableIndexedOwnedFunctionValues.Header compiled program}
    (head : Receipt (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) caller certificate scope id lowered)
    (environment : Dynamic.Environment) :
    head.lambda.function context evidence environment = formed head.formation environment := by
  simp only [Receipt.lambda, LambdaCallee.function, formed, CallableIndexedLambdaGeneration.closure, head.sameSource]

/-- Actual selected literal grammar for the existing generic Calls/Tree fold. -/
def Head (caller : CallableIndexedOwnedFunctionValues.Header compiled program)
    (certificate : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => Nonempty (Receipt (headers := headers) (registry := registry) (faults := faults)
    (source := source) (context := context) (evidence := evidence) caller certificate scope id lowered)
end Certificates

section Formation
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : CallableIndexedOwnedFunctionValues.Header compiled program)
  (prefixZero : owner.key.capturePrefix = 0)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (head : Receipt (headers := headers) (registry := registry) (faults := faults)
    (source := source) (context := context) (evidence := evidence) caller certificate scope id lowered)
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {ξ : Renaming}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ (bridge.pool initial))
  (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world heap store)

/-- The formation records of the literal callee: its copies, closure and formed
state. -/
abbrev CalleeRecord :=
  FormedRecord head.formation complete globals (bridge.pool initial) owner prefixZero packet.observed packet.carried
    packet.bundle related agrees typed
    (model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))

local notation "Record" => CalleeRecord owner caller prefixZero profile complete globals head bridge initial packet related
  agrees typed

/-- This exact producer retains prefix one, immutable owner, full captures and
original named history, for a formed closure over its copies. No generic model
witness is substituted. -/
def formedReceipt (formedRecord : Record) :=
  of_formation head.formation profile complete globals slots (bridge.pool initial) owner prefixZero packet.observed
    packet.carried packet.bundle related agrees typed heaps formedRecord

local notation "C" => formedReceipt owner caller prefixZero profile complete globals slots head bridge initial packet related agrees typed heaps

/-- The actual producer evaluates its own complete emitted callee expression,
copying the captured cells. Native determinism in the existing parent inversion
matches this exact carrier. -/
theorem formed_receipts (formedRecord : Record) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap head.callee
      (.closure (formed head.formation formedRecord.captured)) formedRecord.finalHeap ∧
    Dynamic.EnvironmentCopies source environment heap formedRecord.captured formedRecord.finalHeap ∧
    Evaluates actual store (head.compiler.calleeCode.expression.rename ξ)
      (.inRight .word (value (C formedRecord).code (C formedRecord).captured.embedding (C formedRecord).history.native
        (C formedRecord).capturedActual)) formedRecord.finalStore := by
  have sourceValue := formedRecord.source program
    (by change Dynamic.OrdinaryRequirementLayout head.formation.code.sourceNode.requirements head.formation.code.sourceNode.coercions []
        rw [head.formation.requirements, head.formation.coercions]; rfl) head.formation.coercions
  refine ⟨?_, ?_, ?_⟩
  · change Dynamic.ExpressionEvaluates program context evidence (CallableIndexedNamedGeneration.source caller.named)
        environment heap head.formation.code.id (.closure (formed head.formation formedRecord.captured)) formedRecord.finalHeap at sourceValue
    simpa only [head.sameSource, head.formation.identifier] using sourceValue
  · have copy := formedRecord.copy
    change Dynamic.EnvironmentCopies (CallableIndexedNamedGeneration.source caller.named) environment heap formedRecord.captured
      formedRecord.finalHeap at copy
    simpa only [head.sameSource] using copy
  · exact Eq.mp (congrArg (fun expression => Evaluates actual store expression
      (.inRight .word (value (actualCode head.formation environment) formedRecord.embedding
        (historyAt head.formation (CallableIndexedOwnedLambdaViewHeads.nested_entry (bridge.pool initial) owner prefixZero
          packet.observed packet.carried packet.bundle globals) environment).native formedRecord.closureActual)) formedRecord.finalStore)
      (congrArg (fun output : SourceCoreBasic.LoweredExpr => output.expression.rename ξ) head.formation.emitted)) formedRecord.evaluated

include bridge in
/-- The caller witness reaches every administrative extension through the owned
pool and its returned wrapper. -/
theorem caller_transition {index : ProtectedStateTransition.Index} (state : callerProtocol.State index)
    {nextMap : LocationMap} {nextWorld : StoreTyping} {nextHeap : Dynamic.Heap} {nextStore : Store}
    (maps : LocationMap.Extends index.mapping nextMap) (worlds : WorldExtends index.world nextWorld)
    (frame : AdministrativePreserved index.mapping index.store nextMap nextStore)
    (metadata : Dynamic.HeapMetadataExtend index.heap nextHeap) :
    ProtectedStateTransition.Transition callerProtocol state (index.extend nextMap nextWorld nextHeap nextStore) := by
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedFunctionState.protocol headers keys)
    (CallableIndexedOwnedFunctionState.administrativeTransport headers keys) (bridge.pool state)
    maps worlds frame metadata
  obtain ⟨returned, _, callerRelated⟩ := bridge.restore state reached maps worlds frame metadata related
  exact ⟨returned, callerRelated⟩

local notation "P" => callerProtocol
local notation "B" => bridge
local notation "F" => CallableIndexedOwnedFunctionValues.model headers keys registry faults profile

include prefixZero complete globals slots related agrees typed heaps in
/-- Pointwise Source head: genuine initial Source typing and all-row stability
remain real input receipts. The literal callee copies its captured cells and
the caller witness follows to the formed state; then ordered arguments,
parameter allocation, body and restoration return their exact reached
witnesses. -/
theorem preserves_bounded
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context heap) (stable : StableRows (bridge.pool initial))
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
    (budget : Nat)
    (arguments : Below budget (ProtectedStateTransition.PreservesAt P
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry F)
      program context evidence source certificate faults))
    (bodies : ∀ formedRecord : Record,
      ∀ reached : (P).State ⟨scope, formedRecord.finalMap, formedRecord.finalWorld, formedRecord.finalHeap,
        formedRecord.finalStore, canonical⟩,
      (P).Relates initial reached →
      SourceContinuations (source := source) (context := context) (evidence := evidence)
        (environment := environment) (ids := head.ids) profile (C formedRecord) (head.selected environment).escaped B
        reached budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment heap id outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry F)
        finalMap finalWorld head.compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry F finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition P initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨calleeSize, argumentsSize, callSize, calleeCaptured, calleeHeap, calleeTrace, calleeCopy, suffix,
      calleeSmall, argumentsSmall, callWithin⟩ :=
    suffix_of_source head.compiler.found head.compiler.originalForm head.parent.coercions
      head.compiler.argumentCoercions head.parent.arity head.lambda unique wellFormed runtime covers locals heapTyped
      head.sourceArguments head.sourceCount trace
  obtain ⟨formedRecord⟩ := formation_exists head.formation complete globals slots (bridge.pool initial) owner prefixZero
    packet.observed packet.carried packet.bundle related agrees typed heaps
  obtain ⟨_sourceCallee, sourceCopy, nativeCallee⟩ := formed_receipts owner caller prefixZero profile complete globals slots
    head bridge initial packet related agrees typed heaps formedRecord
  obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional calleeCopy sourceCopy
  rw [head.function_eq] at calleeTrace suffix
  obtain ⟨reached, reachedRelated⟩ := caller_transition bridge initial formedRecord.maps formedRecord.worlds formedRecord.frame formedRecord.copy.metadata_extends
  have captures : FunctionValues.SourceCapturesValid formedRecord.finalHeap (.closure (formed head.formation formedRecord.captured)) :=
    formedRecord.copy.agrees locals
  let selected := head.selected environment
  obtain ⟨sourceSize, value, finalStore, finalMap, finalWorld, sourceParent, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, transition⟩ :=
    preserves_bounded_with_continuations profile head.compiler head.prepared head.parent (C formedRecord)
      selected.children selected.nativeTypes selected.escaped selected.rawResult selected.nativeResult
      (related.extend formedRecord.maps formedRecord.worlds) formedRecord.heaps (locals.mono formedRecord.copy.metadata_extends) captures agrees
      (typed.weaken formedRecord.worlds) wellFormed runtime covers (heapTyped.copy formedRecord.copy) head.sourceArguments head.sourceCount
      B reached (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) stable formedRecord.frame) budget
      arguments (bodies formedRecord reached reachedRelated) initial reachedRelated formedRecord.maps formedRecord.worlds formedRecord.frame formedRecord.copy.metadata_extends
      calleeTrace nativeCallee selected.stageAccepted selected.arityAccepted suffix
      (Nat.le_trans (Nat.le_of_lt argumentsSmall) within) (Nat.le_trans callWithin within)
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩

include prefixZero complete globals slots related agrees typed heaps in
/-- Native reflection uses the real literal producer's evaluation in the
original parent completion inversion. It retains original strict native
argument/body children and an independently graded whole Source trace. -/
theorem reflects_bounded
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context heap) (stable : StableRows (bridge.pool initial))
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (budget : Nat)
    (arguments : Below budget (ProtectedStateTransition.ReflectsAt P
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry F)
      program context evidence source certificate faults))
    (bodies : ∀ formedRecord : Record,
      ∀ reached : (P).State ⟨scope, formedRecord.finalMap, formedRecord.finalWorld, formedRecord.finalHeap,
        formedRecord.finalStore, canonical⟩,
      (P).Relates initial reached →
      NativeContinuations (source := source) (context := context) (evidence := evidence)
        (environment := environment) (ids := head.ids) profile (C formedRecord) (head.selected environment).escaped B
        reached budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment heap id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry F)
        finalMap finalWorld head.compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry F finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition P initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨formedRecord⟩ := formation_exists head.formation complete globals slots (bridge.pool initial) owner prefixZero
    packet.observed packet.carried packet.bundle related agrees typed heaps
  obtain ⟨sourceCallee, _sourceCopy, nativeCallee⟩ := formed_receipts owner caller prefixZero profile complete globals
    slots head bridge initial packet related agrees typed heaps formedRecord
  obtain ⟨calleeSize, calleeTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size sourceCallee
  obtain ⟨reached, reachedRelated⟩ := caller_transition bridge initial formedRecord.maps formedRecord.worlds formedRecord.frame formedRecord.copy.metadata_extends
  have captures : FunctionValues.SourceCapturesValid formedRecord.finalHeap (.closure (formed head.formation formedRecord.captured)) :=
    formedRecord.copy.agrees locals
  let selected := head.selected environment
  exact reflects_bounded_with_continuations profile head.compiler head.prepared head.parent (C formedRecord)
    selected.children selected.nativeTypes selected.escaped selected.rawResult selected.nativeResult
    (related.extend formedRecord.maps formedRecord.worlds) formedRecord.heaps (locals.mono formedRecord.copy.metadata_extends) captures agrees
    (typed.weaken formedRecord.worlds) wellFormed runtime covers (heapTyped.copy formedRecord.copy) head.sourceArguments head.sourceCount
    B reached (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) stable formedRecord.frame) budget
    arguments (bodies formedRecord reached reachedRelated) initial reachedRelated formedRecord.maps formedRecord.worlds formedRecord.frame formedRecord.copy.metadata_extends
    calleeTrace nativeCallee selected.stageAccepted selected.arityAccepted completed within

end Formation
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedIndirectHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedIndirectBodies
/-! Closed body continuations are a separate specialization of the selected
indirect interface. They apply the existing named/literal body family to the
same authentic future captures and actual ordered argument post. The shared
mixed-origin closer can instead supply its strict IH through the generic
selected interface; this module does not enlarge that existing family's grammar. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedIndirectBodies
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedLambdaValues RecursiveNamedLambdaFormationHeads
open CallableIndexedOwnedFunctionState
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (prefixZero : owner.key.capturePrefix = 0)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
variable
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (ranks : CallableIndexedOwnedFunctionValues.Header compiled program → Nat)
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}

variable (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame},
      (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers owner.key.locations owner.key.capturePrefix (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost) →
      (CallableIndexedOwnedNamedCanonicalEntries.condition (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header) entry →
      MatchProfileWith (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor true header.solved context header.function.evidence)
        (CallableIndexedOwnedNestedNamedFamilyClosure.certificates (headers := headers) (registry := registry) (faults := faults) ranks header)
        diagnosticPolicy header (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)


open CallableIndexedOwnedIndirectExpressionHeads
universe u
variable
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {ids : List ExpressionId}
  {callerScope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {sourceType : TypeSystem.Ty} {carrier : Value} {type : Ty}
  (closure : ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    mapping world function sourceType carrier type)
  (sameOwner : closure.owner = owner) (prefixOne : closure.callerPrefix = 1)
  (principalGlobals : closure.support.1.globals = compiled.indexed.base.globals.length)
  (bodyUninitialized : ∀ id location, faults (.uninitializedLocation location) (closure.code.reasonAt id))
  (bodyMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((closure.code.reasonAt id).add tag))
  (bodyEscaped : faults .controlEscapedFunction closure.code.compilation.internalReason)
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (initial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)

include prefixZero complete globals slots sameLayouts extension faithful observations functionTypes
  owners uninitialized missing escaped profiles sameOwner prefixOne principalGlobals bodyUninitialized bodyMissing in
/-- Each real argument post obtains a closed Source continuation at its exact
parameter Entry and body. The authentic selected owner and full captured
canonical prefix are preserved through the actual argument effects. -/
theorem source_continuations (budget : Nat) :
    SourceContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := ids) profile closure bodyEscaped bridge initial budget := by
  subst owner
  intro middleMap middleWorld maps worlds arguments payloads middle middleStore argumentState
    parameterArguments middleHeaps sourceCaptures frame metadata related sourceArgumentsSize sourceArguments
  let future := closure.extend maps worlds
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers future.owner.key.locations 1 future.scope future.captured.canonical future.owner.key.frameLocation := by
    have same : future.callerPrefix = 1 := prefixOne
    simpa only [same] using future.globals
  exact CallableIndexedOwnedNestedLambdaBodyBounds.source_continuation
    closure.owner prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
    owners uninitialized missing escaped ranks profiles future.support.1 principalGlobals
    future.captured future.code future.history future.inputs future.support.2.2.receipt
    bodyUninitialized bodyMissing bodyEscaped observed future.origin.historyMetadata (bridge.pool argumentState) budget

include prefixZero complete globals slots sameLayouts extension faithful observations functionTypes
  uninitialized missing escaped profiles sameOwner prefixOne principalGlobals bodyUninitialized bodyMissing in
/-- Native continuation reflection consumes the actual Prefix and reached
body pool, keeping independent Source grades and exact final restoration. -/
theorem native_continuations (budget : Nat) :
    NativeContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := ids) profile closure bodyEscaped bridge initial budget := by
  subst owner
  intro middleMap middleWorld maps worlds arguments payloads middle middleStore argumentState
    parameterArguments middleHeaps sourceCaptures frame metadata related sourceArgumentsSize sourceArguments
  let future := closure.extend maps worlds
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers future.owner.key.locations 1 future.scope future.captured.canonical future.owner.key.frameLocation := by
    have same : future.callerPrefix = 1 := prefixOne
    simpa only [same] using future.globals
  exact CallableIndexedOwnedNestedLambdaBodyBounds.native_continuation
    closure.owner prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
    uninitialized missing escaped ranks profiles future.support.1 principalGlobals
    future.captured future.code future.history future.inputs future.support.2.2.receipt
    bodyUninitialized bodyMissing bodyEscaped observed future.origin.historyMetadata (bridge.pool argumentState) budget

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedIndirectBodies
end

import Solcore.SourceSemantics.CoreLowering.CallContractCertificates
import Solcore.SourceSemantics.CoreLowering.CallableAppliedViewProvenance

/-! A caller frame built from retained source metadata, with a scoped
representation refinement. Its source ledger records closure parameters and
source result staging, exact named metadata selection, and builtin bypass.
World-independent origin receipts supplement an existing semantic payload
model; they never establish closure code correctness merely from Core typing.

The original source alignment of contextual lambdas is explicit. The metadata
factory's boolean caller check alone is not silently used as a propositional
TypedSource equality. Whole recursive stage-frame propagation remains separate. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLedger
open Frontend Frontend.SourceInference SourceCoreStageContracts GeneralHeap
open CallContractCertificates

inductive Binds (plan : Plan) : Dynamic.Value → SourceContract → Prop where
  | closure {function : Dynamic.Closure} {contract : SourceContract}
      (parameters : contract.parameters = function.parameters)
      (result : contract.stagedResult = true ↔ Staging.ComptimeOnlyType function.resultType) :
      Binds plan (.closure function) contract
  | named {function : Dynamic.GlobalFunction} {key : Key} {contract : Contract}
      (selected : SourceCompilationPlan.exactInstantiationKey plan function.instantiation = .ok key)
      (prepared : Contract.named plan key = .ok contract) :
      Binds plan (.global function) (semanticContract contract)

theorem Binds.userCallable {plan : Plan} {value : Dynamic.Value} {contract : SourceContract}
    (bound : Binds plan value contract) : Staging.CallBoundary.UserCallable value := by
  cases bound with
  | closure => exact .closure _
  | named => exact .global _

theorem Binds.unique {plan : Plan} {value : Dynamic.Value} {left right : SourceContract}
    (first : Binds plan value left) (second : Binds plan value right) : left = right := by
  cases first with
  | closure parameters result =>
    cases second with
    | closure otherParameters otherResult =>
      cases left with
      | mk leftParameters leftResult =>
        cases right with
        | mk rightParameters rightResult =>
          dsimp only at parameters result otherParameters otherResult
          cases parameters.trans otherParameters.symm
          cases leftResult <;> cases rightResult <;> simp_all
  | named selected prepared =>
    cases second with
    | named otherSelected otherPrepared =>
      cases Except.ok.inj (selected.symm.trans otherSelected)
      cases Except.ok.inj (prepared.symm.trans otherPrepared)
      rfl

/-- Caller stages come from the retained analyzed sidecar. Contracts are read
from original source metadata, independently of the erased Core carrier. -/
def frame (sidecar : Sidecar) : Staging.CallBoundary.Frame where
  stages := CallStageGuard.frame sidecar.caller
  Binds := Binds sidecar.plan
  userCallable := Binds.userCallable
  unique := Binds.unique

/-- Alignment of one actual source closure with its original monomorphic or
contextual lambda factory receipt. `active` is the full cumulative context. -/
inductive LambdaOrigin (plan : Plan) (owner : Key) (id : ExpressionId) :
    TypeSystem.Substitution → Dynamic.Closure → Contract → Prop where
  | original {sidecar : Sidecar} {function : Dynamic.Closure} {contract : Contract}
      (prepared : Contract.lambda sidecar id = .ok contract)
      (receipt : LambdaReceipt sidecar id contract)
      (samePlan : sidecar.plan = plan) (sameOwner : sidecar.caller.key = owner)
      (source : function.source = sidecar.source)
      (parameters : function.parameters = receipt.parameters)
      (result : function.resultType = receipt.result)
      (body : function.body = receipt.body) : LambdaOrigin plan owner id [] function contract
  | contextual {sidecar : Sidecar} {contextual : SourceCoreLocalEvidence.Prepared}
      {function : Dynamic.Closure} {contract : Contract}
      (prepared : Contract.contextualLambda sidecar contextual id = .ok contract)
      (receipt : ContextualLambdaReceipt sidecar contextual id contract)
      (samePlan : sidecar.plan = plan) (sameOwner : sidecar.caller.key = owner)
      (source : function.source = sidecar.source.applySubstitution contextual.substitution)
      (parameters : function.parameters = receipt.parameters.map (TypedBinder.applySubstitution contextual.substitution))
      (result : function.resultType = contextual.substitution.apply receipt.result)
      (body : function.body = receipt.body) :
      LambdaOrigin plan owner id contextual.substitution function contract

  | applied {checked : SourceCoreCompatibleCatalog.Checked}
      {base : SourceCoreCompatibleFunctions.Prepared checked}
      {inputs : SourceCoreCallableAncestryPreparation.Inputs base}
      {callerFrame lexicalFrame : SourceCoreCallablePairedFrames.Frame}
      {caller lexical : SourceCoreCallableAncestryReadRecipes.State} {view target : Core.Word}
      {function : Dynamic.Closure} {contract : Contract}
      (recipe : CallableAppliedViewProvenance.Recipe inputs callerFrame lexicalFrame caller lexical view target)
      (canonical : CallableAppliedViewProvenance.CanonicalHeader inputs recipe.read.template contract)
      (retained : recipe.read.descriptor.contract = some contract)
      (samePlan : base.plan = plan) (sameOwner : recipe.read.template.owner = owner)
      (sameId : recipe.read.template.id = id)
      (source : function.source = (recipe.read.after lexical).metadata.source)
      (parameters : function.parameters = recipe.applied.parameters.map
        (TypedBinder.applySubstitution recipe.read.substitution))
      (result : function.resultType = recipe.read.substitution.apply recipe.applied.resultType)
      (body : function.body = recipe.applied.body) :
      LambdaOrigin plan owner id recipe.read.template.active function contract

theorem LambdaOrigin.binds {plan : Plan} {owner : Key} {id : ExpressionId} {active : TypeSystem.Substitution}
    {function : Dynamic.Closure} {contract : Contract}
    (origin : LambdaOrigin plan owner id active function contract) : Binds plan (.closure function) (semanticContract contract) := by
  cases origin with
  | original _ receipt _ _ _ parameters result _ =>
    refine .closure (receipt.parameters_eq.trans parameters.symm) ?_
    change contract.stagedResult = true ↔ Staging.ComptimeOnlyType function.resultType
    rw [receipt.stagedResult, result]
    exact SourceStageAnalysis.typeIsComptimeOnly_eq_true_iff _
  | contextual _ receipt _ _ _ parameters result _ =>
    refine .closure (receipt.parameters_eq.trans parameters.symm) ?_
    change contract.stagedResult = true ↔ Staging.ComptimeOnlyType function.resultType
    rw [receipt.stagedResult, result]
    exact SourceStageAnalysis.typeIsComptimeOnly_eq_true_iff _

  | applied recipe canonical _ _ _ _ _ parameters result _ =>
    refine .closure ((recipe.contract_parameters canonical).trans parameters.symm) ?_
    change contract.stagedResult = true ↔ Staging.ComptimeOnlyType function.resultType
    rw [recipe.contract_result canonical, result]
    exact SourceStageAnalysis.typeIsComptimeOnly_eq_true_iff _

/-- Static metadata provenance for the visible descriptor of a value. The
underlying payload model remains responsible for its code/capture meaning. -/
inductive OriginRep (plan : Plan) (table : SourceCoreStageCodebook.Table) : Dynamic.Value → Core.Value → Prop where
  | closure {function : Dynamic.Closure} {raw : Core.Value} {entry : SourceCoreStageCodebook.Entry}
      {owner : Key} {id : ExpressionId} {active : TypeSystem.Substitution} {contract : Contract}
      (member : entry ∈ table.entries) (entryOrigin : entry.origin = .lambda owner id active)
      (retained : entry.contract = some contract) (origin : LambdaOrigin plan owner id active function contract) :
      OriginRep plan table (.closure function) (.pair raw (.word entry.id))
  | named {function : Dynamic.GlobalFunction} {raw : Core.Value} {entry : SourceCoreStageCodebook.Entry}
      {key : Key} {contract : Contract}
      (member : entry ∈ table.entries) (entryOrigin : entry.origin = .named key)
      (retained : entry.contract = some contract)
      (selected : SourceCompilationPlan.exactInstantiationKey plan function.instantiation = .ok key)
      (prepared : Contract.named plan key = .ok contract) :
      OriginRep plan table (.global function) (.pair raw (.word entry.id))
  | builtin {function : Dynamic.BuiltinFunction} {raw : Core.Value} {entry : SourceCoreStageCodebook.Entry}
      (member : entry ∈ table.entries) (entryOrigin : entry.origin = .builtin function.id)
      (retained : entry.contract = none) :
      OriginRep plan table (.builtin function) (.pair raw (.word entry.id))

/-- Add stage provenance to an existing value relation. This is intentionally
not a model admitting arbitrary values solely from `RuntimeValueHasType`. -/
def model {catalog : SourceCoreDataCatalog.Catalog} (underlying : GenericHeap.PayloadModel catalog)
    (plan : Plan) (table : SourceCoreStageCodebook.Table) : GenericHeap.PayloadModel catalog where
  Represents mapping world type source core payload :=
    underlying.Represents mapping world type source core payload ∧ OriginRep plan table source core
  projection related := underlying.projection related.1
  runtime_hasType related := underlying.runtime_hasType related.1
  extend related maps worlds := ⟨underlying.extend related.1 maps worlds, related.2⟩

/-- A static row receipt records actual `prepareGuard` success. Factory
extraction for complete tables is kept separate from source value semantics. -/
structure Row (sidecar : Sidecar) (site : SourceCoreCallableContracts.Callsite)
    (call : ExpressionId) (arguments : List ExpressionId) (entry : SourceCoreStageCodebook.Entry) where
  decision : SourceCoreStageCodebook.Decision
  found : site.rowAt? entry.id = some decision
  entry_eq : decision.entry = entry
  prepared : ∀ contract, entry.contract = some contract → ∃ guard,
    prepareGuard sidecar call contract = .ok guard ∧ decision.guard = some guard ∧ guard.arguments = arguments
  builtin : entry.contract = none → decision.guard = none

/-- Each actual retained entry has its original guarded row at this caller.
This predicate contains metadata-factory equations, not child evaluations. -/
def Rows (sidecar : Sidecar) (site : SourceCoreCallableContracts.Callsite)
    (call : ExpressionId) (arguments : List ExpressionId) : Prop :=
  ∀ entry, entry ∈ site.table.entries → Nonempty (Row sidecar site call arguments entry)

theorem dispatch {sidecar : Sidecar} {site : SourceCoreCallableContracts.Callsite}
    {call : ExpressionId} {arguments : List ExpressionId} {source : Dynamic.Value} {carrier : Core.Value}
    (rows : Rows sidecar site call arguments)
    (origin : OriginRep sidecar.plan site.table source carrier)
    {contract : SourceContract} (bound : (frame sidecar).Binds source contract) :
    Nonempty (CallStageBoundary.Dispatch (frame sidecar) site call arguments source carrier) := by
  cases origin with
  | @closure function raw entry owner id active original member _ retained provenance =>
    obtain ⟨row⟩ := rows entry member
    obtain ⟨guard, prepared, attached, arguments_eq⟩ := row.prepared original retained
    obtain ⟨receipt⟩ := guard_of_accepted prepared
    refine ⟨⟨raw, entry.id, row.decision, guard, rfl, row.found, attached, receipt.call, arguments_eq, ?_, ?_⟩⟩
    · rw [receipt.sidecar_eq]; rfl
    · rw [receipt.contract_eq]
      exact provenance.binds
  | @named function raw entry key original member _ retained selected prepared =>
    obtain ⟨row⟩ := rows entry member
    obtain ⟨guard, checked, attached, arguments_eq⟩ := row.prepared original retained
    obtain ⟨receipt⟩ := guard_of_accepted checked
    refine ⟨⟨raw, entry.id, row.decision, guard, rfl, row.found, attached, receipt.call, arguments_eq, ?_, ?_⟩⟩
    · rw [receipt.sidecar_eq]; rfl
    · rw [receipt.contract_eq]
      exact Binds.named selected prepared
  | builtin => cases bound

theorem covers {catalog : SourceCoreDataCatalog.Catalog} (underlying : GenericHeap.PayloadModel catalog)
    {sidecar : Sidecar} {site : SourceCoreCallableContracts.Callsite} {call : ExpressionId}
    {arguments : List ExpressionId} (rows : Rows sidecar site call arguments)
    (sourceType : TypeSystem.Ty) (type : Core.Ty) :
    CallStageBoundary.Covers (model underlying sidecar.plan site.table) (frame sidecar) site call arguments sourceType type := by
  intro mapping world source carrier contract represented bound
  exact dispatch rows represented.2 bound

end Solcore.SourceSemantics.CoreLowering.CallableLedger

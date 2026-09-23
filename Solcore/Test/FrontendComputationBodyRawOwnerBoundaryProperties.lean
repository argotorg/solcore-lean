import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation

/-! These artificial child interfaces test the generic contract, not Core
semantics. A cost interface need not erase into an uncosted interface, nor must
an uncosted interface possess a cost. Raw absence is not a fault classification. -/
set_option autoImplicit false
namespace Tests.FrontendComputationBodyRawOwnerBoundary
open Solcore Solcore.Frontend
private abbrev Eval := LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop
private abbrev Cost := LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop
private def allRaw : Eval := fun _ _ _ _ _ _ => True
private def noRaw : Eval := fun _ _ _ _ _ _ => False
private def allCost : Cost := fun _ _ _ _ _ _ _ => True
private def noCost : Cost := fun _ _ _ _ _ _ _ => False
private def returned (span : Syntax.SourceSpan) (e : Syntax.Expr) : Syntax.Block := ⟨span,[⟨span,.returnStmt (some e)⟩]⟩

theorem generic_uncosted_transport_requires_no_cost_existence_bridge
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (o : Resolved.DeclarationId) (names : LocalNameTable) (env : Resolved.Environment)
    (span : Syntax.SourceSpan) (e : Syntax.Expr) (s t : Core.Store) (v : Core.Value) :
    ComputationReturnTreeEvaluates allRaw o names env s (returned span e) v t ∧
    ComputationReturnTreeEvaluates allRaw (mapping o) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) env) s (returned span e) v t ∧
    ¬ ∃ cost, ComputationReturnTreeEvaluatesWithCost noCost o names env s (returned span e) v t cost := by
  have original : ComputationReturnTreeEvaluates allRaw o names env s (returned span e) v t := .expression trivial
  refine ⟨original,(computationReturnTreeEvaluates_mapOwner_iff mapping injective (by intros; rfl)).mpr original,?_⟩
  rintro ⟨cost,h⟩
  cases h with | expression impossible => exact impossible
theorem generic_cost_transport_requires_no_uncosted_erasure_bridge
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (o : Resolved.DeclarationId) (names : LocalNameTable) (env : Resolved.Environment)
    (span : Syntax.SourceSpan) (e : Syntax.Expr) (s t : Core.Store) (v : Core.Value) (cost : Nat) :
    ComputationReturnTreeEvaluatesWithCost allCost o names env s (returned span e) v t cost ∧
    ComputationReturnTreeEvaluatesWithCost allCost (mapping o) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) env) s (returned span e) v t cost ∧
    ¬ ComputationReturnTreeEvaluates noRaw o names env s (returned span e) v t := by
  have original : ComputationReturnTreeEvaluatesWithCost allCost o names env s (returned span e) v t cost := .expression trivial
  refine ⟨original,(computationReturnTreeEvaluatesWithCost_mapOwner_iff mapping injective (by intros; rfl)).mpr original,?_⟩
  intro h
  cases h with | expression impossible => exact impossible

private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RawOwnerBoundary",by decide⟩],by decide⟩⟩,133⟩
private def ident : Resolved.LocalId := ⟨owner,0⟩
private def shift (id : Resolved.DeclarationId) : Resolved.DeclarationId := {id with declarationIndex := id.declarationIndex+10}
private theorem injective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; cases modules; cases indices; rfl
private def names : LocalNameTable := [("x",ident)]
private def reference (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.identifier ⟨s,"x"⟩⟩
private def fixedRaw : Eval := fun table _ _ _ _ _ => table.lookup? "x"=some ident
private def fixedCost : Cost := fun table _ _ _ _ _ cost => table.lookup? "x"=some ident ∧ cost=7
private theorem changedLookup :
    ¬ (LocalNameTable.mapIds (ownerLocalIdMap shift) names).lookup? "x"=some ident := by decide
theorem injective_nonsurjective_owner_maps_still_require_the_supplied_child_covariance
    (span : Syntax.SourceSpan) (env : Resolved.Environment) (s t : Core.Store) (v : Core.Value) :
    Function.Injective shift ∧ (¬ Function.Surjective shift) ∧
    ComputationReturnTreeEvaluates fixedRaw owner names env s (returned span (reference span)) v t ∧
    ComputationReturnTreeEvaluatesWithCost fixedCost owner names env s (returned span (reference span)) v t 7 ∧
    ¬ ComputationReturnTreeEvaluates fixedRaw (shift owner) (LocalNameTable.mapIds (ownerLocalIdMap shift) names)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap shift) env) s (returned span (reference span)) v t ∧
    ¬ ∃ cost, ComputationReturnTreeEvaluatesWithCost fixedCost (shift owner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) names) (Resolved.LocalScope.mapIds (ownerLocalIdMap shift) env)
      s (returned span (reference span)) v t cost := by
  refine ⟨injective,?_,.expression rfl,.expression ⟨rfl,rfl⟩,?_,?_⟩
  · intro surjective
    obtain ⟨id,same⟩ := surjective { owner with declarationIndex := 0 }
    have impossible := congrArg Resolved.DeclarationId.declarationIndex same
    change id.declarationIndex+10=0 at impossible
    omega
  · intro h
    cases h with | expression child => exact changedLookup child
  · rintro ⟨cost,h⟩
    cases h with | expression child => exact changedLookup child.1
theorem the_failed_covariance_premises_are_genuinely_false
    (span : Syntax.SourceSpan) (env : Resolved.Environment) (s t : Core.Store) (v : Core.Value) :
    ¬ (fixedRaw (LocalNameTable.mapIds (ownerLocalIdMap shift) names)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap shift) env) s (reference span) v t ↔
      fixedRaw names env s (reference span) v t) ∧
    ¬ (fixedCost (LocalNameTable.mapIds (ownerLocalIdMap shift) names)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap shift) env) s (reference span) v t 7 ↔
      fixedCost names env s (reference span) v t 7) :=
  ⟨fun covariance => changedLookup (covariance.mpr rfl),fun covariance => changedLookup (covariance.mpr ⟨rfl,rfl⟩).1⟩

private def unsupported (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.literal ⟨s,.string "no raw rule"⟩⟩
private theorem absent (span : Syntax.SourceSpan) (o : Resolved.DeclarationId) (table : LocalNameTable)
    (env : Resolved.Environment) (s t : Core.Store) (v : Core.Value) :
    ¬ RecursiveComputationReturnTreeEvaluates o table env s (returned span (unsupported span)) v t := by
  intro h
  cases h with | expression child => cases child with | pure pureChild => cases pureChild with | wordLiteral meaning => cases meaning
private theorem costAbsent (span : Syntax.SourceSpan) (o : Resolved.DeclarationId) (table : LocalNameTable)
    (env : Resolved.Environment) (s t : Core.Store) (v : Core.Value) (cost : Nat) :
    ¬ RecursiveComputationReturnTreeEvaluatesWithCost o table env s (returned span (unsupported span)) v t cost := by
  intro h
  cases h with | expression child => cases child with | pure pureChild => cases pureChild with | wordLiteral meaning => cases meaning
theorem a_real_unsupported_child_has_no_raw_success_or_cost_after_owner_transport
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (inj : Function.Injective mapping)
    (span : Syntax.SourceSpan) (o : Resolved.DeclarationId) (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) :
    (¬ ∃ v t, RecursiveComputationReturnTreeEvaluates (mapping o) (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) env) s (returned span (unsupported span)) v t) ∧
    (¬ ∃ v t cost, RecursiveComputationReturnTreeEvaluatesWithCost (mapping o) (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) env) s (returned span (unsupported span)) v t cost) := by
  constructor
  · rintro ⟨v,t,h⟩
    exact absent span o table env s t v ((computationReturnTreeEvaluates_mapOwner_iff mapping inj
      (recursiveLocalComputationEvaluates_mapIds_iff _ (ownerLocalIdMap_injective mapping inj))).mp h)
  · rintro ⟨v,t,cost,h⟩
    exact costAbsent span o table env s t v cost ((computationReturnTreeEvaluatesWithCost_mapOwner_iff mapping inj
      (recursiveLocalComputationEvaluatesWithCost_mapIds_iff _ (ownerLocalIdMap_injective mapping inj))).mp h)
end Tests.FrontendComputationBodyRawOwnerBoundary

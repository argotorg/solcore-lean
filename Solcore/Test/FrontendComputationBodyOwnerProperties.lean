import Solcore.Frontend.ComputationReturnTreeOwnerProperties
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputationRenamingProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Core.FuelResumptionProperties

/-! Original repeated typed/inferred lets, discard, scope barrier, conditional
and grouped-wildcard/default rows have independent typing and elaboration.
Only this variable/literal fixture preserves stores. No raw owner law is used. -/
set_option autoImplicit false
namespace Tests.FrontendComputationBodyOwner
open Solcore Solcore.Frontend
private def types (a : Core.Ty) : TypeNameTable := [(["A"],a)]
private def named (s : Syntax.SourceSpan) : Syntax.TypeExpr := ⟨s,.named ⟨s,⟨⟨⟨s,"A"⟩,[]⟩⟩⟩ none⟩
private def ref (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.identifier ⟨s,"x"⟩⟩
private def zero := Core.Word.ofNatModulo 0
private def literal (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.literal ⟨s,.decimal "0"⟩⟩
private theorem denotes (s : Syntax.SourceSpan) : WordLiteralDenotes ⟨s,.decimal "0"⟩ zero :=
  .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) rfl) .nil)
private def condition (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.binary (literal s) ⟨s,.equal⟩ (literal s)⟩
private def guardCore : Core.Expr := .binary .wordEq (.word zero) (.word zero)
private def returned (s : Syntax.SourceSpan) : Syntax.Block := ⟨s,[⟨s,.returnStmt (some (ref s))⟩]⟩
private def arm (s : Syntax.SourceSpan) : Syntax.MatchCase := ⟨s,⟨⟨s,.group ⟨s,.wildcard s⟩⟩,returned s⟩⟩
private def matched (s : Syntax.SourceSpan) : Syntax.Block :=
  ⟨s,[⟨s,.matchWith ⟨s,⟨literal s,[]⟩⟩ ⟨s,⟨[arm s],some (returned s)⟩⟩⟩]⟩
private def scopeBlock (s : Syntax.SourceSpan) : Syntax.Block := ⟨s,[⟨s,.block (matched s).value⟩]⟩
private def statements (s : Syntax.SourceSpan) : Nat → List Syntax.Statement
  | 0 => [⟨s,.expression (ref s) true⟩,⟨s,.ifThen (condition s) (scopeBlock s) (some (returned s))⟩]
  | n+1 => ⟨s,.letDecl ⟨s,"x"⟩ (some (named s)) (some (ref s))⟩::
      ⟨s,.letDecl ⟨s,"x"⟩ none (some (ref s))⟩::statements s n
private def beforeDiscard : Core.Expr := .ifE guardCore (.letE (.word zero) (.var 1)) (.var 0)
private def core : Nat → Core.Expr
  | 0 => .letE (.var 0) (.ifE guardCore (.letE (.word zero) (.var 2)) (.var 1))
  | n+1 => .letE (.var 0) (.letE (.var 0) (core n))
private theorem discardShift : beforeDiscard.weakenAt 0=.ifE guardCore (.letE (.word zero) (.var 2)) (.var 1) := by
  simp [beforeDiscard,guardCore,Core.Expr.weakenAt]
private theorem protection (s : Syntax.SourceSpan) (i : LocalTypeInputs) :
    ComputationNamesProtected (i.names.map Prod.fst) (scopeBlock s) :=
  computationBlockPreservesNames_iff.mp (by simp only [scopeBlock,computationBlockPreservesNames])
private theorem guardElab (s : Syntax.SourceSpan) (i : LocalTypeInputs) :
    RecursiveLocalComputationElaborates i.names i.context (condition s) guardCore .bool :=
  .pure (.equal (.wordLiteral (denotes s)) (.wordLiteral (denotes s))) (.binary .word .word) (.binary .word .word)
private theorem guardTyped (s : Syntax.SourceSpan) (i : LocalTypeInputs) :
    RecursiveLocalComputationHasType i.names i.context (condition s) .bool :=
  .pure (.equal (.wordLiteral (denotes s)) (.wordLiteral (denotes s)))
private theorem matchElab (s : Syntax.SourceSpan) (a : Core.Ty) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (leaf : RecursiveLocalComputationElaborates i.names i.context (ref s) (.var 0) a) :
    RecursiveComputationReturnTreeElaborates (types a) o i (matched s) (.letE (.word zero) (.var 1)) a := by
  refine .wordMatch (entries := [(arm s,none,.var 0)]) (defaultEntry := some (returned s,.var 0))
    (.pure (.wordLiteral (denotes s)) .word .word) rfl ?_ (.inl rfl) ?_ rfl ?_ ?_
  · intro entry member; simp only [List.mem_singleton] at member; subst entry; exact .group (.wildcard rfl)
  · intro entry member; simp only [List.mem_singleton] at member; subst entry; exact .expression leaf
  · intro entry member; simp only [Option.toList_some,List.mem_singleton] at member; subst entry; exact .expression leaf
  · simp [Core.Expr.weakenAt]
private theorem matchTyped (s : Syntax.SourceSpan) (a : Core.Ty) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (leaf : RecursiveLocalComputationHasType i.names i.context (ref s) a) :
    RecursiveComputationReturnTreeHasType (types a) o i (matched s) a := by
  refine .wordMatch (.pure (.wordLiteral (denotes s))) ?_ (.inl rfl) (.inl rfl) ?_ ?_
  · intro entry member; simp only [List.mem_singleton] at member; subst entry; exact ⟨none,.group (.wildcard rfl)⟩
  · intro entry member; simp only [List.mem_singleton] at member; subst entry; exact .expression leaf
  · intro entry member; simp only [Option.toList_some,List.mem_singleton] at member; subst entry; exact .expression leaf
private theorem elaborated (s : Syntax.SourceSpan) (a : Core.Ty) (o : Resolved.DeclarationId)
    (n : Nat) (i : LocalTypeInputs) (leaf : RecursiveLocalComputationElaborates i.names i.context (ref s) (.var 0) a) :
    RecursiveComputationReturnTreeElaborates (types a) o i ⟨s,statements s n⟩ (core n) a := by
  induction n generalizing i with
  | zero =>
      change RecursiveComputationReturnTreeElaborates _ _ _ _ (.letE (.var 0) _) _
      rw [← discardShift]
      exact .discard leaf (.conditional (guardElab s i) (protection s i) (.block (matchElab s a o i leaf)) (.expression leaf))
  | succ n ih =>
      exact .binding (.named .head) leaf (.inferred (.pure (.identifier .head) (.var .head) (.var .head))
        (ih ((i.bindFresh o "x" a).bindFresh o "x" a) (.pure (.identifier .head) (.var .head) (.var .head))))
private theorem typed (s : Syntax.SourceSpan) (a : Core.Ty) (o : Resolved.DeclarationId)
    (n : Nat) (i : LocalTypeInputs) (leaf : RecursiveLocalComputationHasType i.names i.context (ref s) a) :
    RecursiveComputationReturnTreeHasType (types a) o i ⟨s,statements s n⟩ a := by
  induction n generalizing i with
  | zero => exact .discard leaf (.conditional (guardTyped s i) (protection s i) (.block (matchTyped s a o i leaf)) (.expression leaf))
  | succ n ih =>
      exact .binding (.named .head) leaf (.inferred (.pure (.identifier .head .head))
        (ih ((i.bindFresh o "x" a).bindFresh o "x" a) (.pure (.identifier .head .head))))
private theorem guardCost (s : Syntax.SourceSpan) (names : LocalNameTable) (e : Resolved.Environment) (store : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost names e store (condition s) (.bool true) store 5 :=
  .pure (.equal (.wordLiteral (denotes s)) (.wordLiteral (denotes s)))
private def freshNames (o : Resolved.DeclarationId) (names : LocalNameTable) := ("x",Resolved.freshLocalId o (names.map Prod.snd))::names
private def freshEnv (o : Resolved.DeclarationId) (names : LocalNameTable) (e : Resolved.Environment) (v : Core.Value) :=
  (Resolved.freshLocalId o (names.map Prod.snd),v)::e
private theorem raw (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (n : Nat)
    (names : LocalNameTable) (e : Resolved.Environment) (v : Core.Value) (store : Core.Store)
    (leaf : RecursiveLocalComputationEvaluatesWithCost names e store (ref s) v store 1) :
    RecursiveComputationReturnTreeEvaluatesWithCost o names e store ⟨s,statements s n⟩ v store (6*n+14) := by
  induction n generalizing names e with
  | zero =>
      refine .discard (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (expressionCost := 1) (tailCost := 11) leaf ?_
      exact .ifTrue (conditionCost := 5) (branchCost := 4) (guardCost s names e store)
        (.block (ComputationReturnTreeEvaluatesWithCost.wordMatch (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
          (scrutineeCost := 1) (branchCost := 1) (tests := 0)
          (.pure (.wordLiteral (denotes s))) (.wildcard (.group (.wildcard rfl))) (.expression leaf)))
  | succ n ih =>
      have count : 6*(n+1)+14=1+(1+(6*n+14)+2)+2 := by omega
      rw [count]
      exact .binding leaf (.inferred (.pure (.identifier .head .head))
        (ih (freshNames o (freshNames o names)) (freshEnv o (freshNames o names) (freshEnv o names e v) v)
          (.pure (.identifier .head .head))))
private theorem manual (n : Nat) (v : Core.Value) (rest : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (6*n+14) ⟨.eval (core n) (v::rest),k,store⟩ ⟨.ret v,k,store⟩ := by
  induction n generalizing rest k with
  | zero =>
      exact CostStepComposition.letE (.cons (.var rfl) .refl)
        (CostStepComposition.ifTrue (CostStepComposition.binary (.cons .word .refl) (.cons .word .refl) rfl)
          (CostStepComposition.letE (.cons .word .refl) (.cons (.var rfl) .refl)))
  | succ n ih =>
      have count : 6*(n+1)+14=1+(1+(6*n+14)+2)+2 := by omega
      rw [count]; exact CostStepComposition.letE (.cons (.var rfl) .refl)
        (CostStepComposition.letE (.cons (.var rfl) .refl) (ih (v::v::rest) k))
private def start (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a : Core.Ty) := i.bindFresh o "x" a
private theorem original (s : Syntax.SourceSpan) (a : Core.Ty) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (n : Nat) :
    RecursiveComputationReturnTreeElaborates (types a) o (start o i a) ⟨s,statements s n⟩ (core n) a :=
  elaborated s a o n (start o i a) (.pure (.identifier .head) (.var .head) (.var .head))

theorem original_typing_and_elaboration_are_independently_constructed
    (s : Syntax.SourceSpan) (a : Core.Ty) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (n : Nat) :
    RecursiveComputationReturnTreeHasType (types a) o (start o i a) ⟨s,statements s n⟩ a ∧
    RecursiveComputationReturnTreeElaborates (types a) o (start o i a) ⟨s,statements s n⟩ (core n) a :=
  ⟨typed s a o n (start o i a) (.pure (.identifier .head .head)),original s a o i n⟩
theorem owner_transport_keeps_both_independent_judgments_and_all_original_branches
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (a : Core.Ty) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (n : Nat) :
    let changed := (start o i a).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)
    RecursiveComputationReturnTreeHasType (types a) (mapping o) changed ⟨s,statements s n⟩ a ∧
    RecursiveComputationReturnTreeElaborates (types a) (mapping o) changed ⟨s,statements s n⟩ (core n) a :=
  ⟨(computationReturnTreeHasType_mapOwner_iff mapping injective
      (recursiveLocalComputationHasType_mapIds_iff _ (ownerLocalIdMap_injective mapping injective))).mpr
      (original_typing_and_elaboration_are_independently_constructed s a o i n).1,
    (computationReturnTreeElaborates_mapOwner_iff mapping injective
      (recursiveLocalComputationElaborates_mapIds_iff _ (ownerLocalIdMap_injective mapping injective))).mpr (original s a o i n)⟩
theorem complete_checker_keeps_the_literal_core_after_owner_transport
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (a : Core.Ty) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (n : Nat) :
    elaborateRecursiveComputationReturnTree? (types a) (mapping o)
      ((start o i a).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
      ⟨s,statements s n⟩=some (core n,a) :=
  (elaborateComputationReturnTree?_mapOwner mapping injective elaborateRecursiveLocalComputation?
    (elaborateRecursiveLocalComputation?_mapIds _ (ownerLocalIdMap_injective mapping injective)) _ _ _ _).trans
      ((elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr (original s a o i n))
theorem original_raw_cost_and_handwritten_path_do_not_use_an_owner_transport_law
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (n : Nat) (names : LocalNameTable) (e : Resolved.Environment)
    (v : Core.Value) (rest : Core.Environment) (store : Core.Store) (k : List Core.Frame)
    (leaf : RecursiveLocalComputationEvaluatesWithCost names e store (ref s) v store 1) :
    RecursiveComputationReturnTreeEvaluatesWithCost o names e store ⟨s,statements s n⟩ v store (6*n+14) ∧
    Core.Steps (6*n+14) ⟨.eval (core n) (v::rest),k,store⟩ ⟨.ret v,k,store⟩ :=
  ⟨raw s o n names e v store leaf,manual n v rest store k⟩
theorem complete_machine_records_use_literal_core_and_unchanged_actual_values
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (a : Core.Ty) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (n fuel : Nat)
    (e : Resolved.Environment) (store : Core.Store) :
    (elaborateRecursiveComputationReturnTree? (types a) (mapping o)
      ((start o i a).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) ⟨s,statements s n⟩).map
      (fun (ce,t) => (t,Core.runStateful fuel (.initial ce (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) e).values store)))=
      some (a,Core.runStateful fuel (.initial (core n) e.values store)) := by
  rw [complete_checker_keeps_the_literal_core_after_owner_transport mapping injective s a o i n,Option.map_some,Resolved.LocalScope.values_mapIds]
theorem exact_fuel_and_all_genuine_resumptions_keep_actual_payloads
    (n fuel extra : Nat) (v : Core.Value) (rest : Core.Environment) (store : Core.Store) :
    (Core.runStateful fuel (.initial (core n) (v::rest) store)=.done v store ↔ 6*n+14≤fuel) ∧
    ∀ cp, Core.runStateful fuel (.initial (core n) (v::rest) store)=.outOfFuel cp →
      Core.runStateful extra cp=Core.runStateful (fuel+extra) (.initial (core n) (v::rest) store) :=
  ⟨(manual n v rest store []).runStateful_done_iff,fun _ stopped => Core.runStateful_resume stopped extra⟩
theorem first_initializer_finishes_in_its_original_environment
    (n : Nat) (v : Core.Value) (rest : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    let e := v::rest
    let cp : Core.State := ⟨.ret v,.letBody (.letE (.var 0) (core n)) e::k,store⟩
    Core.runStateful 2 ⟨.eval (core (n+1)) e,k,store⟩=.outOfFuel cp ∧
    ∀ extra, Core.runStateful extra cp=Core.runStateful (2+extra) ⟨.eval (core (n+1)) e,k,store⟩ := by
  have path : Core.Steps 2 ⟨.eval (core (n+1)) (v::rest),k,store⟩
      ⟨.ret v,.letBody (.letE (.var 0) (core n)) (v::rest)::k,store⟩ := .cons .enterLet (.cons (.var rfl) .refl)
  have stopped := Core.runStateful_outOfFuel_complete path (show Core.advance _=.next _ from rfl)
  exact ⟨stopped,Core.runStateful_resume stopped⟩
end Tests.FrontendComputationBodyOwner

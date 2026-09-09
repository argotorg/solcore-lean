import Solcore.Frontend.ComputationReturnTreeTypeExtensionProperties
import Solcore.Frontend.ComputationReturnTreeTypingProperties
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.LocalExpressionCostStepComposition
import Solcore.Core.FuelResumptionProperties

/-! Original symbolic annotations, shadowed names, conditional arms and match
rows are constructed independently of checking. These spans are arbitrary fields,
not a parser claim. The explicit variable/literal fixture alone preserves stores. -/
set_option autoImplicit false
namespace Tests.FrontendComputationTypeTable
open Solcore Solcore.Frontend
private def named (s : Syntax.SourceSpan) : Syntax.TypeExpr :=
  ⟨s,.named ⟨s,⟨⟨⟨s,"Payload"⟩,[]⟩⟩⟩ none⟩
private def types (a : Core.Ty) : TypeNameTable := [(["Payload"],a),(["Payload"],.bool)]
private def annotation (s : Syntax.SourceSpan) : Nat → Syntax.TypeExpr
  | 0 => ⟨s,.tuple [named s,⟨s,.tuple []⟩,named s]⟩
  | d+1 => ⟨s,.function s ⟨s,[named s]⟩ (some ⟨s,[annotation s d]⟩)⟩
private def annotatedType (a : Core.Ty) : Nat → Core.Ty
  | 0 => .product a (.product .unit a)
  | d+1 => .function a (annotatedType a d)
private theorem meaning (s : Syntax.SourceSpan) (a : Core.Ty) (d : Nat) :
    StructuralTypeDenotes (types a) (annotation s d) (annotatedType a d) := by
  induction d with
  | zero => exact .many (.named .head) (.pair .unit (.named .head))
  | succ d ih => exact .functionReturns (.named .head) (.single ih)
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s,.identifier ⟨s,name⟩⟩
private def zero := Core.Word.ofNatModulo 0
private def literal (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.literal ⟨s,.decimal "0"⟩⟩
private theorem denotes (s : Syntax.SourceSpan) : WordLiteralDenotes ⟨s,.decimal "0"⟩ zero :=
  .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) rfl) .nil)
private def condition (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.binary (literal s) ⟨s,.equal⟩ (literal s)⟩
private def guardCore : Core.Expr := .binary .wordEq (.word zero) (.word zero)
private theorem guardElab (s : Syntax.SourceSpan) (i : LocalTypeInputs) :
    RecursiveLocalComputationElaborates i.names i.context (condition s) guardCore .bool :=
  .pure (.equal (.wordLiteral (denotes s)) (.wordLiteral (denotes s))) (.binary .word .word) (.binary .word .word)
private def returned (s : Syntax.SourceSpan) (name : String) : Syntax.Block := ⟨s,[⟨s,.returnStmt (some (ref s name))⟩]⟩
private def arm (s : Syntax.SourceSpan) (name : String) : Syntax.MatchCase :=
  ⟨s,⟨⟨s,.group ⟨s,.wildcard s⟩⟩,returned s name⟩⟩
private def matched (s : Syntax.SourceSpan) (name : String) : Syntax.Block :=
  ⟨s,[⟨s,.matchWith ⟨s,⟨literal s,[]⟩⟩ ⟨s,⟨[arm s name],some (returned s name)⟩⟩⟩]⟩
private def statements (s : Syntax.SourceSpan) (d : Nat) : List String → String → List Syntax.Statement
  | [],previous => [⟨s,.ifThen (condition s) (matched s previous) (some (returned s previous))⟩]
  | name::rest,previous => ⟨s,.letDecl ⟨s,name⟩ (some (annotation s d)) (some (ref s previous))⟩ :: statements s d rest name
private def core : Nat → Core.Expr
  | 0 => .ifE guardCore (.letE (.word zero) (.var 1)) (.var 0)
  | n+1 => .letE (.var 0) (core n)
private theorem matchElab (s : Syntax.SourceSpan) (table : TypeNameTable) (o : Resolved.DeclarationId)
    (i : LocalTypeInputs) (name : String) (t : Core.Ty)
    (leaf : RecursiveLocalComputationElaborates i.names i.context (ref s name) (.var 0) t) :
    RecursiveComputationReturnTreeElaborates table o i (matched s name) (.letE (.word zero) (.var 1)) t := by
  refine .wordMatch (entries := [(arm s name,none,.var 0)]) (defaultEntry := some (returned s name,.var 0))
    (.pure (.wordLiteral (denotes s)) .word .word) rfl ?_ (.inl rfl) ?_ rfl ?_ ?_
  · intro entry member; simp only [List.mem_singleton] at member; subst entry; exact .group (.wildcard rfl)
  · intro entry member; simp only [List.mem_singleton] at member; subst entry; exact .expression leaf
  · intro entry member; simp only [Option.toList_some,List.mem_singleton] at member; subst entry; exact .expression leaf
  · simp [Core.Expr.weakenAt]
private theorem elaborated (s : Syntax.SourceSpan) (a : Core.Ty) (d : Nat) (o : Resolved.DeclarationId)
    (names : List String) (previous : String) (i : LocalTypeInputs)
    (leaf : RecursiveLocalComputationElaborates i.names i.context (ref s previous) (.var 0) (annotatedType a d)) :
    RecursiveComputationReturnTreeElaborates (types a) o i
      ⟨s,statements s d names previous⟩ (core names.length) (annotatedType a d) := by
  induction names generalizing previous i with
  | nil =>
      exact .conditional (guardElab s i)
        (computationBlockPreservesNames_iff.mp (by simp only [matched,computationBlockPreservesNames]))
        (matchElab s (types a) o i previous _ leaf) (.expression leaf)
  | cons name rest ih =>
      exact .binding (meaning s a d) leaf
        (ih name (i.bindFresh o name (annotatedType a d)) (.pure (.identifier .head) (.var .head) (.var .head)))
private theorem guardCost (s : Syntax.SourceSpan) (table : LocalNameTable) (e : Resolved.Environment) (store : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost table e store (condition s) (.bool true) store 5 :=
  .pure (.equal (.wordLiteral (denotes s)) (.wordLiteral (denotes s)))
private theorem raw (s : Syntax.SourceSpan) (d : Nat) (o : Resolved.DeclarationId)
    (names : List String) (previous : String) (table : LocalNameTable) (e : Resolved.Environment)
    (value : Core.Value) (store : Core.Store)
    (leaf : RecursiveLocalComputationEvaluatesWithCost table e store (ref s previous) value store 1) :
    RecursiveComputationReturnTreeEvaluatesWithCost o table e store ⟨s,statements s d names previous⟩ value store (3*names.length+11) := by
  induction names generalizing previous table e with
  | nil =>
      exact .ifTrue (conditionCost := 5) (branchCost := 4) (guardCost s table e store)
        (ComputationReturnTreeEvaluatesWithCost.wordMatch (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
          (scrutineeCost := 1) (branchCost := 1) (tests := 0)
          (.pure (.wordLiteral (denotes s))) (.wildcard (.group (.wildcard rfl))) (.expression leaf))
  | cons name rest ih =>
      have count : 3*(name::rest).length+11=1+(3*rest.length+11)+2 := by simp only [List.length_cons]; omega
      rw [count]
      exact .binding leaf (ih name ((name,Resolved.freshLocalId o (table.map Prod.snd))::table)
        ((Resolved.freshLocalId o (table.map Prod.snd),value)::e) (.pure (.identifier .head .head)))
private theorem manual (n : Nat) (value : Core.Value) (retained : Core.Environment)
    (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (3*n+11) ⟨.eval (core n) (value::retained),k,store⟩ ⟨.ret value,k,store⟩ := by
  induction n generalizing retained k with
  | zero =>
      exact CostStepComposition.ifTrue
        (CostStepComposition.binary (.cons .word .refl) (.cons .word .refl) rfl)
        (CostStepComposition.letE (.cons .word .refl) (.cons (.var rfl) .refl))
  | succ n ih =>
      have count : 3*(n+1)+11=1+(3*n+11)+2 := by omega
      rw [count]; exact CostStepComposition.letE (.cons (.var rfl) .refl) (ih (value::retained) k)
private def starting (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a : Core.Ty) (d : Nat) :=
  i.bindFresh o "x" (annotatedType a d)
private theorem original (s : Syntax.SourceSpan) (a : Core.Ty) (d : Nat) (o : Resolved.DeclarationId)
    (i : LocalTypeInputs) (names : List String) :
    RecursiveComputationReturnTreeElaborates (types a) o (starting o i a d)
      ⟨s,statements s d names "x"⟩ (core names.length) (annotatedType a d) :=
  elaborated s a d o names "x" (starting o i a d) (.pure (.identifier .head) (.var .head) (.var .head))

theorem nested_original_annotations_and_all_branches_are_independent
    (s : Syntax.SourceSpan) (a : Core.Ty) (d : Nat) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (names : List String) :
    StructuralTypeDenotes (types a) (annotation s d) (annotatedType a d) ∧
    RecursiveComputationReturnTreeElaborates (types a) o (starting o i a d)
      ⟨s,statements s d names "x"⟩ (core names.length) (annotatedType a d) :=
  ⟨meaning s a d,original s a d o i names⟩
theorem independent_typing_and_exact_core_survive_extension
    (s : Syntax.SourceSpan) (a : Core.Ty) (d : Nat) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (names : List String)
    (next : TypeNameTable) (extension : TypeNameTable.Extends (types a) next) :
    RecursiveComputationReturnTreeHasType next o (starting o i a d) ⟨s,statements s d names "x"⟩ (annotatedType a d) ∧
    RecursiveComputationReturnTreeElaborates next o (starting o i a d)
      ⟨s,statements s d names "x"⟩ (core names.length) (annotatedType a d) := by
  have el := original s a d o i names
  have ht := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,el⟩
  exact ⟨ht.extend_types extension,el.extend_types extension⟩
theorem successful_append_keeps_the_whole_original_body
    (s : Syntax.SourceSpan) (a : Core.Ty) (d : Nat) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (names : List String) (extras : TypeNameTable) :
    elaborateRecursiveComputationReturnTree? (types a++extras) o (starting o i a d)
      ⟨s,statements s d names "x"⟩=some (core names.length,annotatedType a d) :=
  elaborateComputationReturnTree?_some_of_extends (TypeNameTable.Extends.append_right _ _)
    ((elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr (original s a d o i names))
theorem fresh_prepend_keeps_the_whole_original_body
    (s : Syntax.SourceSpan) (a extra : Core.Ty) (d : Nat) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (names : List String) (key : List String) (fresh : key≠["Payload"]) :
    elaborateRecursiveComputationReturnTree? ((key,extra)::types a) o (starting o i a d)
      ⟨s,statements s d names "x"⟩=some (core names.length,annotatedType a d) :=
  elaborateComputationReturnTree?_some_of_extends
    (TypeNameTable.Extends.cons_fresh _ _ _ (by simpa [types] using fresh))
    ((elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr (original s a d o i names))
private theorem hiddenMutual (a hidden : Core.Ty) :
    TypeNameTable.Extends (types a) [(["Payload"],a),(["Payload"],hidden)] ∧
    TypeNameTable.Extends [(["Payload"],a),(["Payload"],hidden)] (types a) := by
  constructor <;> intro key type found <;> cases found with
  | head => exact .head
  | tail different found => cases found with
    | head => exact False.elim (different rfl)
    | tail _ found => cases found
theorem hidden_conflicting_rows_preserve_every_optional_body_result
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (a hidden : Core.Ty) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (source : Syntax.Block) :
    elaborateComputationReturnTree? checkChild (types a) o i source=
      elaborateComputationReturnTree? checkChild [(["Payload"],a),(["Payload"],hidden)] o i source :=
  elaborateComputationReturnTree?_eq_of_mutual_extends (hiddenMutual a hidden).1 (hiddenMutual a hidden).2 o i source
theorem actual_raw_cost_and_manual_path_need_no_type_table
    (s : Syntax.SourceSpan) (d : Nat) (o : Resolved.DeclarationId) (names : List String)
    (previous : String) (table : LocalNameTable) (e : Resolved.Environment) (value : Core.Value) (retained : Core.Environment)
    (store : Core.Store) (k : List Core.Frame)
    (leaf : RecursiveLocalComputationEvaluatesWithCost table e store (ref s previous) value store 1) :
    RecursiveComputationReturnTreeEvaluatesWithCost o table e store ⟨s,statements s d names previous⟩ value store (3*names.length+11) ∧
    Core.Steps (3*names.length+11) ⟨.eval (core names.length) (value::retained),k,store⟩ ⟨.ret value,k,store⟩ :=
  ⟨raw s d o names previous table e value store leaf,manual names.length value retained store k⟩
theorem exact_fuel_and_all_genuine_resumptions_keep_literal_values
    (n fuel extra : Nat) (value : Core.Value) (retained : Core.Environment) (store : Core.Store) :
    (Core.runStateful fuel (.initial (core n) (value::retained) store)=.done value store ↔ 3*n+11≤fuel) ∧
    ∀ cp, Core.runStateful fuel (.initial (core n) (value::retained) store)=.outOfFuel cp →
      Core.runStateful extra cp=Core.runStateful (fuel+extra) (.initial (core n) (value::retained) store) :=
  ⟨(manual n value retained store []).runStateful_done_iff,fun _ stopped => Core.runStateful_resume stopped extra⟩
end Tests.FrontendComputationTypeTable

import Solcore.SourceSemantics.CoreLowering.RecursiveStageArguments

/-! The staged universal reflection interface is instantiated with actual
Boolean compiler receipts. A completed bundle constructs the recursive source
argument trace under an administrative slot. The final machine fixture checks
that an ordinary language failure carrier skips later argument mutations; it
does not stand in for proving a stage guard's metadata. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace Tests.SourceRecursiveStageArguments
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap RecursiveStageMeaning RecursiveStageArguments
open DataExpressionSequence (Tree)

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"expression_sequence", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "expression_sequence.solc" }
  startByte := 0
  endByte := 1 }
private def node (index : Nat) (value : Bool) : ExpressionNode := {
  id := id index, span, type := .bool, form := .reference "boolean" (.builtinBoolean value) }
private def source : TypedSource := {
  owner
  inputs := []
  roots := [.expression (id 0), .expression (id 1), .expression (id 2)]
  nodes := [.expression (node 0 true), .expression (node 1 false), .expression (node 2 true)] }
private def catalog : SourceCoreDataCatalog.Catalog := {}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def model := GenericHeap.finitePayload catalog signatures
private def context : SourceSemantics.Context := .ofSignatures signatures
private def code (value : Bool) : SourceCoreBasic.LoweredExpr := ⟨.bool, LanguageResult.success (.bool value)⟩

private inductive Child : Certificate where
  | boolean {scope expression node name value}
      (found : source.lookupExpression? expression = some node)
      (form : node.form = .reference name (.builtinBoolean value))
      (type : node.type = .bool) (requirements : node.requirements = []) (coercions : node.coercions = []) :
      Child scope expression (code value)

private def frame : Staging.Recursive.Scope := {
  origin := ⟨owner, [], []⟩, source, owned := rfl, context, evidence := []
  guards := {
    stages := ⟨false, .unit, fun _ => some .runtime⟩
    Binds := fun _ _ => False
    userCallable := by intro _ _ impossible; cases impossible
    unique := by intro _ _ _ impossible; cases impossible } }
private def registry : Staging.Recursive.Registry := {
  Closure := fun _ _ => False
  source := by intro _ _ impossible; cases impossible
  context := by intro _ _ impossible; cases impossible
  evidence := by intro _ _ impossible; cases impossible }

private theorem leaf_reflects (program : SourceSemantics.Program) :
    Reflects model program registry frame context Child (fun _ _ => False) := by
  intro scope expression lowered certified foundNode found mapping world admin sourceEnv canonical actual
    before store ξ value finalStore environments heaps locals layout evaluated
  cases certified with
  | @boolean scope expression selected name boolean known form type requirements coercions =>
    have same : foundNode = selected := Option.some.inj (found.symm.trans known)
    subst foundNode
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (show Evaluates actual store
      ((code boolean).expression.rename ξ) (.inRight .word (.bool boolean)) store from .inRight .bool)
    refine ⟨.value (.bool boolean), before, mapping, world, ?_, ?_, heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩
    · apply Staging.Recursive.Expression.atomicValue (node := selected) (lookupExpression?_sound known)
      · rw [form]; exact .reference _ _
      · exact coercions
      · rw [form, requirements]; exact .builtinBoolean rfl
    · rw [type]
      exact .value ⟨rfl, .bool boolean⟩

private theorem tree : Tree frame.source Child [] [id 0, id 1, id 2] [.bool, .bool, .bool]
    [code true, code false, code true] :=
  .cons (node := node 0 true) (by cbv) (Child.boolean (by cbv) rfl rfl rfl rfl)
    (.cons (node := node 1 false) (by cbv) (Child.boolean (by cbv) rfl rfl rfl rfl)
      (.single (node := node 2 true) (by cbv) (Child.boolean (by cbv) rfl rfl rfl rfl)))

private def packed := SourceCoreCalls.packArguments [code true, code false, code true]
private def output : Value := .inRight .word (.pair (.bool true) (.pair (.bool false) (.bool true)))
example : SourceCoreBasic.lowerExpression 4 source [] (id 1) Word.zero = .ok (code false) := by cbv
example : SourceCoreBasic.lowerExpression 4 source [] (id 2) Word.zero = .ok (code true) := by cbv

example : ∃ types, Tree frame.source Child [] [id 0, id 1] types [code true, code false] := by
  let identify := fun (value : Bool) => id (if value then 0 else 1)
  let compile := fun value => SourceCoreBasic.lowerExpression 4 source [] (identify value) Word.zero
  have trueCompiled : compile true = .ok (code true) := by
    change SourceCoreBasic.lowerExpression 4 source [] (id 0) Word.zero = .ok (code true)
    cbv
  have falseCompiled : compile false = .ok (code false) := by
    change SourceCoreBasic.lowerExpression 4 source [] (id 1) Word.zero = .ok (code false)
    cbv
  have compiled : [true, false].mapM compile = .ok [code true, code false] := by
    simp only [List.mapM_cons, List.mapM_nil, trueCompiled, falseCompiled, bind, Except.bind, pure, Except.pure]
  apply Tree.of_mapM identify compile compiled
  intro value lowered accepted
  cases value with
  | false =>
    rw [falseCompiled] at accepted
    cases accepted
    exact ⟨node 1 false, by cbv, Child.boolean (by cbv) rfl rfl rfl rfl⟩
  | true =>
    rw [trueCompiled] at accepted
    cases accepted
    exact ⟨node 0 true, by cbv, Child.boolean (by cbv) rfl rfl rfl rfl⟩

private theorem run : runStateful 100 (.initial packed.expression [.integer 900] []) = .done output [] := by cbv

/-- The Core execution constructs the source vector trace even with an extra
raw administrative environment slot. No source trace is supplied here. -/
example (program : SourceSemantics.Program) : ∃ outcome after finalMap finalWorld,
    Staging.Recursive.Expressions program registry frame context [] ⟨[]⟩ [id 0, id 1, id 2] outcome after ∧
    Result model finalMap finalWorld [.bool, .bool, .bool] [code true, code false, code true]
      (fun _ _ => False) outcome output ∧
    GenericHeap.HeapRepresents model finalMap finalWorld after [] ∧
    LocationMap.Extends [] finalMap ∧ WorldExtends [] finalWorld ∧
    AdministrativePreserved [] [] finalMap [] ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ after := by
  apply RecursiveStageArguments.reflects tree (leaf_reflects program) (canonical := []) (ξ := Renaming.insertion 0)
    (.nil .nil) .empty .nil (by intro index value impossible; simp at impossible)
  simpa [packed, code, SourceCoreCalls.packArguments, LocalSequence.pair, LanguageResult.bind,
    LanguageResult.success, Expr.rename, Expr.weakenAt, Renaming.insertion, Renaming.lift] using
    runStateful_evaluation_sound run

/-- Updating the same captured cell twice observes source order in both the
returned pair and the final store. -/
private def writeThenRead (value : Int) : SourceCoreBasic.LoweredExpr :=
  ⟨.integer, .letE (.storeCell (.var 0) (.integer value)) (LanguageResult.success (.loadCell (.var 1)))⟩
private def mutations := SourceCoreCalls.packArguments [writeThenRead 11, writeThenRead 22]
example : runStateful 100 (.initial mutations.expression [.cellRef .integer 0] [.integer 0]) =
    .done (.inRight .word (.pair (.integer 11) (.integer 22))) [.integer 22] := by cbv

private def failed : SourceCoreBasic.LoweredExpr := ⟨.integer, LanguageResult.failure .integer (.word Word.zero)⟩
private def stops := SourceCoreCalls.packArguments [writeThenRead 11, failed, writeThenRead 22]
example : runStateful 100 (.initial stops.expression [.cellRef .integer 0] [.integer 0]) =
    .done (.inLeft (.product .integer (.product .integer .integer)) (.word Word.zero)) [.integer 11] := by cbv


end Tests.SourceRecursiveStageArguments

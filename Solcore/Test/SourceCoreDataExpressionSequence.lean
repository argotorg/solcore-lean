import Solcore.SourceSemantics.CoreLowering.DataExpressionSequence
import Solcore.SourceSemantics.CoreLowering.Literals

/-! The universal vector reflection theorem is instantiated by an actual
Boolean leaf compiler certificate. Separate machine checks exercise mutation
order, first-fault short circuit and a closure captured under temporary slots. -/

set_option autoImplicit false
set_option maxRecDepth 4096
namespace Tests.SourceCoreDataExpressionSequence
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GenericExpressionMeaning DataExpressionSequence GeneralHeap

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

private theorem unique : NodeOccurrencesUnique source := by
  simp [NodeOccurrencesUnique, nodeOccurrenceIds, source, node, Node.occurrenceId, Node.id, NodeId.occurrenceId, id]

private theorem same_node {expression : ExpressionId} {left right : ExpressionNode}
    (found : source.lookupExpression? expression = some left) (contained : ContainsExpression source expression right) :
    right = left := Option.some.inj ((lookupExpression?_complete unique contained).symm.trans found)

private theorem boolean_no_fault {program : SourceSemantics.Program} {expression : ExpressionId}
    {selected : ExpressionNode} {name : String} {boolean : Bool} {sourceEnv : Dynamic.Environment}
    {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (known : source.lookupExpression? expression = some selected)
    (form : selected.form = .reference name (.builtinBoolean boolean)) (coercions : selected.coercions = [])
    (failed : Dynamic.ExpressionFaults program context [] source sourceEnv before expression reason after) : False := by
  cases failed with
  | missing absent => exact Dynamic.ExpressionAbsentIn.excludes_contains absent (lookupExpression?_sound known)
  | form contained failed =>
    have same := same_node known contained
    subst_vars
    rw [form] at failed
    cases failed
  | coercion contained _ failed =>
    have same := same_node known contained
    subst_vars
    rw [coercions] at failed
    cases failed
  | generalizedLocalRequirement contained other _ _ _ _ _ _ _ =>
    have same := same_node known contained
    subst_vars
    rw [form] at other
    cases other
  | generalizedLocalCoercion contained other _ _ _ _ _ _ _ =>
    have same := same_node known contained
    subst_vars
    rw [form] at other
    cases other

private theorem leaf_preserves (program : SourceSemantics.Program) :
    Preserves model program context [] source Child (fun _ _ => False) := by
  intro scope expression lowered certified foundNode found mapping world admin sourceEnv canonical actual
    before store ξ outcome after environments heaps locals layout execution
  cases certified with
  | @boolean scope expression selected name boolean known form type requirements coercions =>
    have same : foundNode = selected := Option.some.inj (found.symm.trans known)
    subst foundNode
    cases execution with
    | value evaluated =>
      have literal : Literals.Tree source expression (.bool boolean) 1 :=
        .bool (lookupExpression?_sound known) form type requirements coercions
      obtain ⟨rfl, rfl⟩ := literal.source_sound unique evaluated
      refine ⟨.inRight .word (.bool boolean), store, mapping, world, .inRight .bool, ?_, heaps,
        .refl _, .refl _, .refl _ _, .refl _⟩
      rw [type]
      exact .value ⟨rfl, .bool boolean⟩
    | fault failed => exact (boolean_no_fault known form coercions failed).elim

private theorem leaf_reflects (program : SourceSemantics.Program) :
    Reflects model program context [] source Child (fun _ _ => False) := by
  intro scope expression lowered certified foundNode found mapping world admin sourceEnv canonical actual
    before store ξ value finalStore environments heaps locals layout evaluated
  cases certified with
  | @boolean scope expression selected name boolean known form type requirements coercions =>
    have same : foundNode = selected := Option.some.inj (found.symm.trans known)
    subst foundNode
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (show Evaluates actual store
      ((code boolean).expression.rename ξ) (.inRight .word (.bool boolean)) store from .inRight .bool)
    refine ⟨.value (.bool boolean), before, mapping, world, .value ?_, ?_, heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩
    · apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound known)
      · rw [form, requirements, coercions]; exact .builtinBoolean rfl
      · rw [coercions]; exact .nil
    · rw [type]
      exact .value ⟨rfl, .bool boolean⟩

private theorem tree : Tree source Child [] [id 0, id 1, id 2] [.bool, .bool, .bool]
    [code true, code false, code true] :=
  .cons (node := node 0 true) (by cbv) (Child.boolean (by cbv) rfl rfl rfl rfl)
    (.cons (node := node 1 false) (by cbv) (Child.boolean (by cbv) rfl rfl rfl rfl)
      (.single (node := node 2 true) (by cbv) (Child.boolean (by cbv) rfl rfl rfl rfl)))

private def packed := SourceCoreCalls.packArguments [code true, code false, code true]
private def output : Value := .inRight .word (.pair (.bool true) (.pair (.bool false) (.bool true)))
example : SourceCoreBasic.lowerExpression 4 source [] (id 1) Word.zero = .ok (code false) := by cbv
example : SourceCoreBasic.lowerExpression 4 source [] (id 2) Word.zero = .ok (code true) := by cbv

example : ∃ types, Tree source Child [] [id 0, id 1] types [code true, code false] := by
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

private theorem source_trace (program : SourceSemantics.Program) :
    Trace program context [] source [] ⟨[]⟩ [id 0, id 1, id 2]
      (.ok [.bool true, .bool false, .bool true]) ⟨[]⟩ := by
  have first : Literals.Tree source (id 0) (.bool true) 1 :=
    .bool (lookupExpression?_sound (show source.lookupExpression? (id 0) = some (node 0 true) by cbv)) rfl rfl rfl rfl
  have second : Literals.Tree source (id 1) (.bool false) 1 :=
    .bool (lookupExpression?_sound (show source.lookupExpression? (id 1) = some (node 1 false) by cbv)) rfl rfl rfl rfl
  have third : Literals.Tree source (id 2) (.bool true) 1 :=
    .bool (lookupExpression?_sound (show source.lookupExpression? (id 2) = some (node 2 true) by cbv)) rfl rfl rfl rfl
  exact .values (.cons (first.source_evaluates program context [] [] ⟨[]⟩)
    (.cons (second.source_evaluates program context [] [] ⟨[]⟩)
      (.cons (third.source_evaluates program context [] [] ⟨[]⟩) .nil)))

example (program : SourceSemantics.Program) : ∃ value finalStore finalMap finalWorld required,
    (∀ fuel, required ≤ fuel → runStateful fuel
      (.initial (packed.expression.rename (Renaming.insertion 0)) [.integer 900] []) = .done value finalStore) ∧
    Result model finalMap finalWorld [.bool, .bool, .bool] [code true, code false, code true]
      (fun _ _ => False) (.ok [.bool true, .bool false, .bool true]) value ∧
    GenericHeap.HeapRepresents model finalMap finalWorld ⟨[]⟩ finalStore ∧
    LocationMap.Extends [] finalMap ∧ WorldExtends [] finalWorld ∧
    AdministrativePreserved [] [] finalMap finalStore ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ ⟨[]⟩ :=
  tree.preserves_sufficient_fuel (leaf_preserves program) (.nil .nil) .empty .nil
    (by intro index value impossible; simp at impossible) (source_trace program)

/-- The Core execution constructs the source vector trace even with an extra
raw administrative environment slot. No source trace is supplied here. -/
example (program : SourceSemantics.Program) : ∃ outcome after finalMap finalWorld,
    Trace program context [] source [] ⟨[]⟩ [id 0, id 1, id 2] outcome after ∧
    Result model finalMap finalWorld [.bool, .bool, .bool] [code true, code false, code true]
      (fun _ _ => False) outcome output ∧
    GenericHeap.HeapRepresents model finalMap finalWorld after [] ∧
    LocationMap.Extends [] finalMap ∧ WorldExtends [] finalWorld ∧
    AdministrativePreserved [] [] finalMap [] ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ after := by
  apply tree.reflects (leaf_reflects program) (canonical := []) (ξ := Renaming.insertion 0)
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

/-- The second child's closure captures the inserted first payload, so later
application must retain the compiler's shifted reference in its real body. -/
private def captured : SourceCoreBasic.LoweredExpr :=
  ⟨.function .unit .integer, LanguageResult.success (.lambda .unit .integer (.loadCell (.var 1)))⟩
private def makeCapture := SourceCoreCalls.packArguments [writeThenRead 33, captured]
private def invokeCapture : Expr := LanguageResult.bind .integer makeCapture.expression
  (LanguageResult.success (.apply (.second (.var 0)) .unit))
example : infer? [.cell .integer] invokeCapture = some (.sum .word .integer) := by
  simp [invokeCapture, makeCapture, captured, writeThenRead, SourceCoreCalls.packArguments,
    LocalSequence.pair, LanguageResult.bind, LanguageResult.success, Expr.weakenAt]
  decide
example : runStateful 200 (.initial invokeCapture [.cellRef .integer 0] [.integer 0]) =
    .done (.inRight .word (.integer 33)) [.integer 33] := by cbv

end Tests.SourceCoreDataExpressionSequence

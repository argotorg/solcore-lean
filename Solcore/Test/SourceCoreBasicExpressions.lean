import Solcore.SourceSemantics.CoreLowering.BasicExpressions

/-! Concrete certificates for grouping, tuple order, and local-cell reads.
The same failure token deliberately represents two different source locations;
the source derivations below identify the actual first faulting location. -/

set_option autoImplicit false

namespace Tests.SourceCoreBasicExpressions

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"basic_expression_certificate", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def leftBinder : Resolved.LocalId := ⟨owner, 0⟩
private def rightBinder : Resolved.LocalId := ⟨owner, 1⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "basic_expression_certificate.solc" }
  startByte := 0
  endByte := 1
}
private def leftNode : ExpressionNode := {
  id := id 0, span, type := .word, form := .reference "left" (.local leftBinder) }
private def rightNode : ExpressionNode := {
  id := id 1, span, type := .bool, form := .reference "right" (.local rightBinder) }
private def groupNode : ExpressionNode := {
  id := id 2, span, type := .word, form := .group (id 0) }
private def pairNode : ExpressionNode := {
  id := id 3, span, type := .product .word .bool, form := .tuple [id 2, id 1] }
private def rootNode : ExpressionNode := {
  id := id 4, span, type := .product .word .bool, form := .group (id 3) }
private def source : TypedSource := {
  owner
  inputs := [
    { id := leftBinder, name := "left", scheme := .mono .word },
    { id := rightBinder, name := "right", scheme := .mono .bool }]
  roots := [.expression (id 4)]
  nodes := [.expression leftNode, .expression rightNode, .expression groupNode,
    .expression pairNode, .expression rootNode]
}

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def token : Core.Word := word 87
private def scope : SourceCoreLocalCell.Scope := [(rightBinder, .bool), (leftBinder, .word)]
private def resultType : Core.Ty := .product .word .bool
private def code : Core.Expr := Core.LocalSequence.pair .word .bool
  (Core.OptionalCell.read .word (.var 1) token)
  (Core.OptionalCell.read .bool (.var 0) token)

private theorem leftMetadata : BasicExpressions.Metadata source (id 0) leftNode .word := {
  contains := ⟨by simp [source], rfl⟩
  owned := rfl
  types := .word
  requirements := rfl
  coercions := rfl
}
private theorem rightMetadata : BasicExpressions.Metadata source (id 1) rightNode .bool := {
  contains := ⟨by simp [source], rfl⟩
  owned := rfl
  types := .bool
  requirements := rfl
  coercions := rfl
}
private theorem groupMetadata : BasicExpressions.Metadata source (id 2) groupNode .word := {
  contains := ⟨by simp [source], rfl⟩
  owned := rfl
  types := .word
  requirements := rfl
  coercions := rfl
}
private theorem pairMetadata : BasicExpressions.Metadata source (id 3) pairNode resultType := {
  contains := ⟨by simp [source], rfl⟩
  owned := rfl
  types := .product .word .bool
  requirements := rfl
  coercions := rfl
}
private theorem rootMetadata : BasicExpressions.Metadata source (id 4) rootNode resultType := {
  contains := ⟨by simp [source], rfl⟩
  owned := rfl
  types := .product .word .bool
  requirements := rfl
  coercions := rfl
}

private theorem tree : BasicExpressions.Tree source scope token (id 4) resultType code 4 :=
  .group rootMetadata rfl (.pair pairMetadata rfl
    (.group groupMetadata rfl (.localRead leftMetadata rfl rfl rfl))
    (.localRead rightMetadata rfl rfl rfl))

private theorem unique : NodeOccurrencesUnique source := by
  simp [NodeOccurrencesUnique, nodeOccurrenceIds, source, leftNode, rightNode,
    groupNode, pairNode, rootNode, Node.occurrenceId, Node.id, NodeId.occurrenceId, id]

private def world : Core.StoreTyping :=
  [Core.OptionalCell.cellType .word, Core.OptionalCell.cellType .bool]
private def environment : Dynamic.Environment := [(rightBinder, ⟨1⟩), (leftBinder, ⟨0⟩)]
private def coreEnvironment : Core.Environment :=
  [.cellRef (Core.OptionalCell.cellType .bool) 1,
    .cellRef (Core.OptionalCell.cellType .word) 0]
private theorem environments : LocalCell.EnvRepresents world scope environment coreEnvironment :=
  .cons rfl (.cons rfl .nil)

private def presentWord : Dynamic.Cell := { type := .word, value := some (.word (word 5)) }
private def absentWord : Dynamic.Cell := { type := .word, value := none }
private def presentBool : Dynamic.Cell := { type := .bool, value := some (.bool true) }
private def absentBool : Dynamic.Cell := { type := .bool, value := none }
private def successHeap : Dynamic.Heap := ⟨[presentWord, presentBool]⟩
private def leftFailureHeap : Dynamic.Heap := ⟨[absentWord, absentBool]⟩
private def rightFailureHeap : Dynamic.Heap := ⟨[presentWord, absentBool]⟩
private def successStore : Core.Store := [.inRight .unit (.word (word 5)), .inRight .unit (.bool true)]
private def leftFailureStore : Core.Store := [.inLeft .word .unit, .inLeft .bool .unit]
private def rightFailureStore : Core.Store := [.inRight .unit (.word (word 5)), .inLeft .bool .unit]
private def successValue : Core.Value := .inRight .word (.pair (.word (word 5)) (.bool true))
private def failureValue : Core.Value := .inLeft resultType (.word token)

private theorem successHeaps : LocalCell.HeapRepresents successHeap.cells successStore world :=
  .cons (.initialized (.word (word 5))) (.cons (.initialized (.bool true)) .nil)
private theorem leftFailureHeaps : LocalCell.HeapRepresents leftFailureHeap.cells leftFailureStore world :=
  .cons (.uninitialized .word) (.cons (.uninitialized .bool) .nil)
private theorem rightFailureHeaps : LocalCell.HeapRepresents rightFailureHeap.cells rightFailureStore world :=
  .cons (.initialized (.word (word 5))) (.cons (.uninitialized .bool) .nil)

private def Correspondence (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (heap : Dynamic.Heap) (store : Core.Store) : Prop :=
  SourceCoreBasic.lowerExpression 4 source scope (id 4) token = .ok ⟨resultType, code⟩ ∧
  Core.infer? (SourceCoreLocalCell.coreContext scope) code = some (Core.LanguageResult.resultType resultType) ∧
  ∃ sourceOutcome coreValue required,
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap (id 4) sourceOutcome heap ∧
    BasicExpressions.OutcomeRepresents resultType token sourceOutcome coreValue ∧
    (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code coreEnvironment store) = .done coreValue store) ∧
    (∀ fuel result finalStore, Core.runStateful fuel (.initial code coreEnvironment store) = .done result finalStore →
      result = coreValue ∧ finalStore = store)

example (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) : Correspondence program context evidence successHeap successStore :=
  tree.lower_run_preserves unique 4 (by decide) program context evidence environments successHeaps

example (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) : Correspondence program context evidence leftFailureHeap leftFailureStore :=
  tree.lower_run_preserves unique 4 (by decide) program context evidence environments leftFailureHeaps

example (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) : Correspondence program context evidence rightFailureHeap rightFailureStore :=
  tree.lower_run_preserves unique 4 (by decide) program context evidence environments rightFailureHeaps

private theorem leftRead (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (tail : List Dynamic.Cell) :
    Dynamic.ExpressionEvaluates program context evidence source environment ⟨presentWord :: tail⟩
      (id 0) (.word (word 5)) ⟨presentWord :: tail⟩ := by
  apply Dynamic.ExpressionEvaluates.intro leftMetadata.contains
  · exact .local rfl (.tail (by decide) .head) (.intro .head) rfl rfl
  · exact .nil

private theorem groupedLeftRead (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (tail : List Dynamic.Cell) :
    Dynamic.ExpressionEvaluates program context evidence source environment ⟨presentWord :: tail⟩
      (id 2) (.word (word 5)) ⟨presentWord :: tail⟩ := by
  apply Dynamic.ExpressionEvaluates.intro groupMetadata.contains
  · exact .group rfl (leftRead program context evidence tail)
  · exact .nil

/-- Independent source success for the nested grouped tuple. -/
example (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) :
    Dynamic.ExpressionEvaluates program context evidence source environment successHeap (id 4)
      (.product (.word (word 5)) (.bool true)) successHeap := by
  have right : Dynamic.ExpressionEvaluates program context evidence source environment successHeap
      (id 1) (.bool true) successHeap := by
    apply Dynamic.ExpressionEvaluates.intro rightMetadata.contains
    · exact .local rfl .head (.intro (.tail .head)) rfl rfl
    · exact .nil
  have paired : Dynamic.ExpressionEvaluates program context evidence source environment successHeap
      (id 3) (.product (.word (word 5)) (.bool true)) successHeap := by
    apply Dynamic.ExpressionEvaluates.intro pairMetadata.contains
    · exact .tuple rfl (.cons (groupedLeftRead program context evidence [presentBool])
        (.cons right .nil)) (.cons (.singleton _))
    · exact .nil
  apply Dynamic.ExpressionEvaluates.intro rootMetadata.contains
  · exact .group rfl paired
  · exact .nil

/-- Both cells are absent, but the left child faults at location zero. Its
tuple-fault derivation has no premise evaluating the right child. -/
example (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) :
    Dynamic.ExpressionFaults program context evidence source environment leftFailureHeap (id 4)
      (.uninitializedLocation ⟨0⟩) leftFailureHeap := by
  have left : Dynamic.ExpressionFaults program context evidence source environment leftFailureHeap
      (id 0) (.uninitializedLocation ⟨0⟩) leftFailureHeap := by
    apply Dynamic.ExpressionFaults.form leftMetadata.contains
    exact .localUninitialized (owned := []) rfl (.tail (by decide) .head)
      (.intro .head) rfl rfl LocalCell.TypeRepresents.word.not_mapping
  have grouped : Dynamic.ExpressionFaults program context evidence source environment leftFailureHeap
      (id 2) (.uninitializedLocation ⟨0⟩) leftFailureHeap :=
    .form groupMetadata.contains (.group rfl left)
  have paired : Dynamic.ExpressionFaults program context evidence source environment leftFailureHeap
      (id 3) (.uninitializedLocation ⟨0⟩) leftFailureHeap :=
    .form pairMetadata.contains (.tuple rfl (.head grouped))
  exact .form rootMetadata.contains (.group rfl paired)

/-- A successful left read allows the right child to fault at location one. -/
example (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) :
    Dynamic.ExpressionFaults program context evidence source environment rightFailureHeap (id 4)
      (.uninitializedLocation ⟨1⟩) rightFailureHeap := by
  have right : Dynamic.ExpressionFaults program context evidence source environment rightFailureHeap
      (id 1) (.uninitializedLocation ⟨1⟩) rightFailureHeap := by
    apply Dynamic.ExpressionFaults.form rightMetadata.contains
    exact .localUninitialized (owned := []) rfl .head (.intro (.tail .head)) rfl rfl
      LocalCell.TypeRepresents.bool.not_mapping
  have paired : Dynamic.ExpressionFaults program context evidence source environment rightFailureHeap
      (id 3) (.uninitializedLocation ⟨1⟩) rightFailureHeap :=
    .form pairMetadata.contains (.tuple rfl
      (.tail (groupedLeftRead program context evidence [absentBool]) (.head right)))
  exact .form rootMetadata.contains (.group rfl paired)

example : Core.runStateful 100 (.initial code coreEnvironment successStore) = .done successValue successStore := by
  simp only [code, Core.LocalSequence.pair, Core.Expr.weakenAt, Core.LanguageResult.bind,
    Core.LanguageResult.success, Core.LanguageResult.failure, Core.OptionalCell.read]
  rfl

example : Core.runStateful 100 (.initial code coreEnvironment leftFailureStore) = .done failureValue leftFailureStore := by
  simp only [code, Core.LocalSequence.pair, Core.Expr.weakenAt, Core.LanguageResult.bind,
    Core.LanguageResult.success, Core.LanguageResult.failure, Core.OptionalCell.read]
  rfl

example : Core.runStateful 100 (.initial code coreEnvironment rightFailureStore) = .done failureValue rightFailureStore := by
  simp only [code, Core.LocalSequence.pair, Core.Expr.weakenAt, Core.LanguageResult.bind,
    Core.LanguageResult.success, Core.LanguageResult.failure, Core.OptionalCell.read]
  rfl

end Tests.SourceCoreBasicExpressions

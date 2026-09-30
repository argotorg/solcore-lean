import Solcore.SourceSemantics.CoreLowering.BasicStatements

/-! Concrete proof consumption for source `let value: Word; return value;`.
All occurrence, binder and compiler premises are discharged here. -/

set_option autoImplicit false

namespace Tests.SourceCoreBasicCorrespondence

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference Solcore.SourceSemantics

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"basic_correspondence", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder : TypedBinder := { id := ⟨owner, 0⟩, name := "value", scheme := .mono .word }
private def letId : StatementId := ⟨⟨owner, 0⟩⟩
private def readId : ExpressionId := ⟨⟨owner, 1⟩⟩
private def returnId : StatementId := ⟨⟨owner, 2⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "basic_correspondence.solc" }
  startByte := 0
  endByte := 1
}
private def letNode : StatementNode := { id := letId, span, type := .unit, form := .letDecl binder none }
private def readNode : ExpressionNode := {
  id := readId
  span
  type := .word
  form := .reference "value" (.local binder.id)
}
private def returnNode : StatementNode := {
  id := returnId
  span
  type := .word
  form := .returnStmt (some readId)
}
private def source : TypedSource := {
  owner
  inputs := []
  roots := [.statement letId, .statement returnId]
  nodes := [.statement letNode, .expression readNode, .statement returnNode]
}
private def context : SourceSemantics.Context := .ofSignatures {
  functions := []
  implRules := []
  traits := []
  implementations := []
}
private def localContext : SourceSemantics.Context := context.withLocal binder.id binder.scheme

private theorem extension : BinderExtends owner context binder localContext := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {
        binders := by simp [TypeParameterBindersWellFormed, context, Context.ofSignatures]
        quantified_nodup := by simp [binder, TypeSystem.Scheme.mono]
        body := .builtin .word
      }
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl
    }
  · simp [LocalFresh, context, Context.ofSignatures]

private def site : CoreLowering.LocalCell.ReadSite source [(binder.id, .word)] readId .word := {
  node := readNode
  binder := binder.id
  name := "value"
  index := 0
  contains := ⟨by simp [source], rfl⟩
  form := rfl
  owner := rfl
  requirements := rfl
  coercions := rfl
  slot := rfl
  types := .word
}
private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

private def reason : Core.Word := Core.Word.ofNatModulo 41
private def expression : Core.Expr :=
  Core.LocalSequence.letUninitialized .word (Core.OptionalCell.read .word (.var 0) reason)
private def finalHeap : Dynamic.Heap := ⟨[{ type := .word, value := none }]⟩
private def finalStore : Core.Store := [.inLeft .word .unit]

/-- This witness comes from the executable lowerer and independent source
rules together; typed completion is a language failure, never a machine fault. -/
example (program : Program) (trailing : List StatementId) :
    Frontend.SourceCoreBasic.lowerStatements 3 source [] (letId :: returnId :: trailing) .word reason =
        .ok expression ∧
      Dynamic.FunctionStatementsExecuteOutcome program context [] source [] ⟨[]⟩
        (letId :: returnId :: trailing) localContext
        (.fault (.uninitializedLocation ⟨0⟩)) finalHeap ∧
      Core.HasType [] expression (Core.LanguageResult.resultType .word) ∧
      ∃ required,
        (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial expression [] []) =
          .done (.inLeft .word (.word reason)) finalStore) ∧
        (∀ fuel value store, Core.runStateful fuel (.initial expression [] []) = .done value store →
          value = .inLeft .word (.word reason) ∧ store = finalStore) := by
  have letContains : ContainsStatement source letId letNode := ⟨by simp [source], rfl⟩
  have returnContains : ContainsStatement source returnId returnNode := ⟨by simp [source], rfl⟩
  obtain ⟨lowered, faults, _, _, typed, required, completes, reflects⟩ :=
    CoreLowering.BasicStatements.uninitialized_then_return
      (program := program) (context := context) (localContext := localContext) (evidence := [])
      (scope := []) (environment := []) (coreEnvironment := [])
      (heap := ⟨[]⟩) (store := []) (world := []) trailing reason unique
      letContains (by rfl) (by rfl) (by rfl) (by rfl) extension .word
      returnContains (by rfl) (by rfl) site (by rfl) (by rfl) .nil
  exact ⟨lowered, faults, typed [], required, completes, reflects⟩

end Tests.SourceCoreBasicCorrespondence

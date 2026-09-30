import Solcore.Frontend.SourceCoreBasic
import Solcore.SourceSemantics.CoreLowering.BasicStatements
import Solcore.Core.BoundedSafety

/-! A complete compiler/source-semantics consumer for allocation, plain
assignment and return. The source heap and Core store agree after the write;
the generated program is checked and executed, rather than replaced by a
hand-written equivalent for the correspondence claim. -/

set_option autoImplicit false

namespace Tests.SourceCoreBasicStatements

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"basic_statement_meaning", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def binderId : Resolved.LocalId := ⟨owner, 0⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index⟩⟩
private def expression (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "basic_statement_meaning.solc" }
  startByte := 0
  endByte := 1
}
private def binder : TypedBinder := { id := binderId, name := "value", scheme := .mono .bool }
private def assignment : AssignmentResolution := {
  target := { root := binderId, projections := [], type := .bool }
}
private def letNode : StatementNode := {
  id := statement 0, span, type := .unit, form := .letDecl binder none
}
private def assignNode : StatementNode := {
  id := statement 1, span, type := .unit, form := .assignValue assignment .equal (expression 3)
}
private def returnNode : StatementNode := {
  id := statement 2, span, type := .bool, form := .returnStmt (some (expression 4))
}
private def trueNode : ExpressionNode := {
  id := expression 3, span, type := .bool, form := .reference "true" (.builtinBoolean true)
}
private def readNode : ExpressionNode := {
  id := expression 4, span, type := .bool, form := .reference "value" (.local binderId)
}
private def source : TypedSource := {
  owner, inputs := [], roots := [.statement (statement 0), .statement (statement 1),
    .statement (statement 2)]
  nodes := [.statement letNode, .statement assignNode, .statement returnNode,
    .expression trueNode, .expression readNode]
}
private def statements : List StatementId := [statement 0, statement 1, statement 2]
private def reason : Core.Word := Core.Word.ofNatModulo 81
private def code : Core.Expr := Core.LocalSequence.letUninitialized .bool
  (Core.LocalSequence.assign .bool (.var 0) (Core.LanguageResult.success (.bool true))
    (Core.OptionalCell.read .bool (.var 0) reason))
private def coreProgram : Core.Program := {
  resultType := Core.LanguageResult.resultType .bool
  body := code
}

private theorem compiled : SourceCoreBasic.lowerStatements 6 source [] statements .bool reason =
    .ok coreProgram.body := by rfl
private theorem checked : coreProgram.check = true := by
  simp [coreProgram, code, Core.LocalSequence.letUninitialized,
    Core.LocalSequence.assign, Core.OptionalCell.allocate, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure,
    Core.Expr.weakenAt]
  decide
private theorem completed : coreProgram.runStateful 100 =
    .done (.inRight .word (.bool true)) [.inRight .unit (.bool true)] := by
  simp [coreProgram, code, Core.LocalSequence.letUninitialized,
    Core.LocalSequence.assign, Core.OptionalCell.allocate, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure,
    Core.Expr.weakenAt]
  rfl

private theorem letContains : ContainsStatement source (statement 0) letNode :=
  ⟨.head _, rfl⟩
private theorem assignContains : ContainsStatement source (statement 1) assignNode :=
  ⟨.tail _ (.head _), rfl⟩
private theorem returnContains : ContainsStatement source (statement 2) returnNode :=
  ⟨.tail _ (.tail _ (.head _)), rfl⟩
private theorem trueContains : ContainsExpression source (expression 3) trueNode :=
  ⟨.tail _ (.tail _ (.tail _ (.head _))), rfl⟩
private theorem readContains : ContainsExpression source (expression 4) readNode :=
  ⟨.tail _ (.tail _ (.tail _ (.tail _ (.head _)))), rfl⟩

private def absentHeap : Dynamic.Heap := ⟨[{ type := .bool, value := none }]⟩
private def presentHeap : Dynamic.Heap := ⟨[{ type := .bool, value := some (.bool true) }]⟩
private def environment : Dynamic.Environment := [(binderId, ⟨0⟩)]

private theorem source_evaluates (program : SourceSemantics.Program)
    (context localContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (extension : BinderExtends owner context binder localContext) :
    Dynamic.FunctionStatementsExecute program context evidence source [] ⟨[]⟩ statements localContext
      (.returned (.bool true)) presentHeap := by
  have allocated : Dynamic.StatementExecutes program context evidence source [] ⟨[]⟩ (statement 0)
      localContext (.fallthrough environment) absentHeap :=
    .letUninitialized letContains rfl rfl extension .append
  have rhs : Dynamic.ExpressionEvaluates program localContext evidence source environment absentHeap
      (expression 3) (.bool true) absentHeap :=
    .intro trueContains (.builtinBoolean rfl) .nil
  have initial : Dynamic.RootInitialValue ({ type := .bool, value := none } : Dynamic.Cell) none :=
    .uninitialized (by rintro ⟨_, _, impossible⟩; cases impossible)
  have assigned : Dynamic.StatementExecutes program localContext evidence source environment absentHeap
      (statement 1) localContext (.fallthrough environment) presentHeap := by
    apply Dynamic.StatementExecutes.assignValue assignContains rfl
    apply Dynamic.SourcePlaceAssignment.intro
    · exact .intro .head (.intro .head) .nil (.intro .head) initial .nil
    · exact rhs
    · exact .intro (.intro .head) rfl initial (.leaf (.equal none (.bool true)))
        (.intro (.intro .head) .head)
  have returned : Dynamic.StatementExecutes program localContext evidence source environment presentHeap
      (statement 2) localContext (.returned (.bool true)) presentHeap :=
    .returnValue returnContains rfl
      (.intro readContains (.local rfl .head (.intro .head) rfl rfl) .nil)
  exact .cons allocated (.cons assigned
    (.singleton returnContains (by intro value impossible; cases impossible) returned))

/-- The exact actual compiler output has independent source and Core finite
derivations, and their initialized final heaps are structurally related. -/
example (program : SourceSemantics.Program) (context localContext : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment)
    (extension : BinderExtends owner context binder localContext) :
    SourceCoreBasic.lowerStatements 6 source [] statements .bool reason = .ok coreProgram.body ∧
    Dynamic.FunctionStatementsExecute program context evidence source [] ⟨[]⟩ statements localContext
      (.returned (.bool true)) presentHeap ∧
    Core.Evaluates [] [] coreProgram.body (.inRight .word (.bool true)) [.inRight .unit (.bool true)] ∧
    CoreLowering.LocalCell.HeapRepresents presentHeap.cells [.inRight .unit (.bool true)]
      [Core.OptionalCell.cellType .bool] :=
  ⟨compiled, source_evaluates program context localContext evidence extension,
    Core.runStateful_evaluation_sound completed, .cons (.initialized (.bool true)) .nil⟩

example (fuel : Nat) : (coreProgram.runStateful fuel).HasType coreProgram.resultType :=
  Core.Program.checked_runStateful_has_type checked fuel

example (fuel additional : Nat) (checkpoint : Core.State)
    (exhausted : coreProgram.runStateful fuel = .outOfFuel checkpoint) :
    Core.runStateful additional checkpoint = coreProgram.runStateful (fuel + additional) :=
  Core.runStateful_resume exhausted additional

end Tests.SourceCoreBasicStatements

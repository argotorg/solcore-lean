import Solcore.SourceSemantics.CoreLowering.LoopStatementCertificates

/-! Extraction from actual default lowering, with no assumed child trees or
execution derivations. The fixtures cover scoped while bodies, both branch
shapes, break/continue, assignment, both local allocation forms, and function
versus nested-list tail conventions. A for loop is accepted by the compiler
but deliberately outside this certificate's static grammar. -/

set_option autoImplicit false

namespace Tests.SourceCoreLoopStatementCertificates

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open LoopStatements.Default

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"loop_certificates", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def binder (index : Nat) : TypedBinder :=
  { id := ⟨owner, index⟩, name := "local", scheme := .mono .word }
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "loop_certificates.solc" }, startByte := 0, endByte := 1 }
private def expressionNode (index : Nat) (type : TypeSystem.Ty) (form : ExpressionForm) : Node :=
  .expression { id := exprId index, span, type, form }
private def statementNode (index : Nat) (type : TypeSystem.Ty) (form : StatementForm) : Node :=
  .statement { id := stmtId index, span, type, form }
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reasonAt (id : ExpressionId) : Core.Word := word (id.occurrence.index + 50)
private def fellThrough : Core.Word := word 99
private def escaped : Core.Word := word 100
private def compilation : SourceCorePrimitive.Context := { solvedRequirements := [] }
private def context : SourceSemantics.Context := .ofSignatures {
  functions := [], implRules := [], traits := [], implementations := [] }
private theorem aligned : BasicStatements.ScopeContextAligned [] context :=
  BasicStatements.ScopeContextAligned.empty _
private def assignment : AssignmentResolution :=
  { target := { root := (binder 0).id, projections := [], type := .word } }
private def statements : List StatementId := [stmtId 0, stmtId 1, stmtId 8]

/-- The inner scope has two locals; assignment addresses the outer local at
index two. The loop body's locals are absent from the outer implicit return. -/
private def source (flag withElse : Bool) : TypedSource := {
  owner, inputs := [], roots := statements.map .statement
  nodes := [
    expressionNode 0 .word (.literal (.decimal "7")),
    expressionNode 1 .word (.literal (.decimal "9")),
    expressionNode 2 .bool (.reference "flag" (.builtinBoolean flag)),
    expressionNode 3 .word (.reference "inner" (.local (binder 2).id)),
    expressionNode 4 .word (.reference "outer" (.local (binder 0).id)),
    statementNode 0 .unit (.letDecl (binder 0) (some (exprId 0))),
    statementNode 1 .unit (.whileLoop (exprId 2) [stmtId 2, stmtId 3]),
    statementNode 2 .unit (.letDecl (binder 1) none),
    statementNode 3 .unit (.block [stmtId 4, stmtId 5, stmtId 7]),
    statementNode 4 .unit (.letDecl (binder 2) (some (exprId 1))),
    statementNode 5 .unit (.ifThen (exprId 2) [stmtId 6]
      (if withElse then some [stmtId 9] else none)),
    statementNode 6 .unit .continueStmt,
    statementNode 7 .unit (.assignValue assignment .equal (exprId 3)),
    statementNode 8 .word (.expression (exprId 4) false),
    statementNode 9 .unit .breakStmt
  ] }

private def flow (flag withElse : Bool) : Core.Expr :=
  Core.LocalSequence.letInitialized (Core.LocalLoop.controlType .word) .word
    (Core.LanguageResult.success (.word (word 7)))
    (Core.LocalLoop.sequence .word
      (Core.LocalLoop.whileLoop .word (Core.LanguageResult.success (.bool flag))
        (Core.LocalSequence.letUninitialized .word
          (Core.LocalLoop.sequence .word
            (Core.LocalSequence.letInitialized (Core.LocalLoop.controlType .word) .word
              (Core.LanguageResult.success (.word (word 9)))
              (Core.LocalLoop.sequence .word
                (Core.LocalLoop.conditional .word (Core.LanguageResult.success (.bool flag))
                  (Core.LocalLoop.continuing .word)
                  (if withElse then Core.LocalLoop.breaking .word else Core.LocalLoop.fallthrough .word))
                (Core.LocalSequence.assign (Core.LocalLoop.controlType .word) (.var 2)
                  (Core.OptionalCell.read .word (.var 0) (reasonAt (exprId 3)))
                  (Core.LocalLoop.fallthrough .word))))
            (Core.LocalLoop.fallthrough .word))) escaped)
      (Core.LocalLoop.returnValue .word (Core.OptionalCell.read .word (.var 0) (reasonAt (exprId 4)))))

private theorem unique (flag withElse : Bool) : NodeOccurrencesUnique (source flag withElse) := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  cases flag <;> cases withElse <;> decide

private theorem noFor (flag withElse : Bool) : NoForLoops (source flag withElse) := by
  intro id node found initializer condition post body
  have member := (lookupStatement?_sound found).1
  simp [source, expressionNode, statementNode] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp

private theorem accepted (flag withElse : Bool) :
    SourceCoreLoops.lowerFlowStatementsWithPolicy (defaultPolicy compilation) 20 (source flag withElse)
      [] statements .word reasonAt true escaped = .ok (flow flag withElse) := by
  cases withElse <;> rfl

example (flag withElse : Bool) : Tree compilation (source flag withElse) reasonAt escaped [] context true
    statements .word (flow flag withElse) :=
  tree_of_lowerFlowStatements aligned (unique flag withElse) (noFor flag withElse) (accepted flag withElse)

example (flag withElse : Bool) : Core.HasType [] (flow flag withElse) (Core.LocalLoop.resultType .word) :=
  (tree_of_lowerFlowStatements aligned (unique flag withElse) (noFor flag withElse) (accepted flag withElse)).hasType .word

private def code (flag withElse : Bool) : Core.Expr :=
  Core.LocalControl.finish .word (Core.LocalLoop.toControl .word (flow flag withElse) escaped)
    (Core.LanguageResult.failure .word (.word fellThrough))

example (flag withElse : Bool) :
    ∃ compiledFlow, code flag withElse = Core.LocalControl.finish .word
      (Core.LocalLoop.toControl .word compiledFlow escaped) (Core.LanguageResult.failure .word (.word fellThrough)) ∧
      Tree compilation (source flag withElse) reasonAt escaped [] context true statements .word compiledFlow := by
  apply tree_of_lowerStatements aligned (unique flag withElse) (noFor flag withElse)
  change (do
    let compiledFlow ← SourceCoreLoops.lowerFlowStatementsWithPolicy (defaultPolicy compilation) 20
      (source flag withElse) [] statements .word reasonAt true escaped
    pure (Core.LocalControl.finish .word (Core.LocalLoop.toControl .word compiledFlow escaped)
      (Core.LanguageResult.failure .word (.word fellThrough)))) = _
  rw [accepted]
  rfl

example (flag withElse : Bool) : Core.HasType [] (code flag withElse)
    (Core.LanguageResult.resultType .word) :=
  Core.LocalControl.finish_hasType .word
    (Core.LocalLoop.toControl_hasType escaped .word
      ((tree_of_lowerFlowStatements aligned (unique flag withElse)
        (noFor flag withElse) (accepted flag withElse)).hasType .word))
    (Core.LanguageResult.failure_hasType .word .word)

private def tailSource : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)]
  nodes := [expressionNode 0 .word (.literal (.decimal "7")),
    statementNode 0 .word (.expression (exprId 0) false)] }
private theorem tailUnique : NodeOccurrencesUnique tailSource := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide
private theorem tailNoFor : NoForLoops tailSource := by
  intro id node found initializer condition post body
  have member := (lookupStatement?_sound found).1
  simp [tailSource, expressionNode, statementNode] at member
  subst node
  simp

example : Tree compilation tailSource reasonAt escaped [] context false [stmtId 0] .word
    (Core.LocalSequence.discard (Core.LocalLoop.controlType .word)
      (Core.LanguageResult.success (.word (word 7))) (Core.LocalLoop.fallthrough .word)) :=
  tree_of_lowerFlowStatementsWithExpression (fuel := 2) aligned tailUnique tailNoFor (by rfl)

example : Tree compilation tailSource reasonAt escaped [] context true [stmtId 0] .word
    (Core.LocalLoop.returnValue .word (Core.LanguageResult.success (.word (word 7)))) :=
  tree_of_lowerFlowStatementsWithExpression (fuel := 2) aligned tailUnique tailNoFor (by rfl)

example : Tree compilation tailSource reasonAt escaped [] context false [] .word
    (Core.LocalLoop.fallthrough .word) :=
  tree_of_lowerFlowStatements (fuel := 0) aligned tailUnique tailNoFor (by rfl)

/-- Break and continue stop traversal of their tail without claiming a finite
loop execution. An explicit return has the same compiler traversal behavior. -/
private def earlySource (form : StatementForm) : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)]
  nodes := [statementNode 0 .unit form] }
private theorem earlyUnique (form : StatementForm) : NodeOccurrencesUnique (earlySource form) := by
  simp [NodeOccurrencesUnique, nodeOccurrenceIds, earlySource, statementNode]
private theorem earlyNoFor (form : StatementForm)
    (notFor : ∀ initializer condition post body, form ≠ .forLoop initializer condition post body) :
    NoForLoops (earlySource form) := by
  intro id node found initializer condition post body
  have member := (lookupStatement?_sound found).1
  simp [earlySource, statementNode] at member
  subst node
  exact notFor initializer condition post body

example : Tree compilation (earlySource .breakStmt) reasonAt escaped [] context false
    [stmtId 0, stmtId 99] .word (Core.LocalLoop.breaking .word) :=
  tree_of_lowerFlowStatements (fuel := 1) aligned (earlyUnique _)
    (earlyNoFor _ (by intros; simp)) (by rfl)
example : Tree compilation (earlySource .continueStmt) reasonAt escaped [] context false
    [stmtId 0, stmtId 99] .word (Core.LocalLoop.continuing .word) :=
  tree_of_lowerFlowStatements (fuel := 1) aligned (earlyUnique _)
    (earlyNoFor _ (by intros; simp)) (by rfl)
example : Tree compilation (earlySource (.returnStmt none)) reasonAt escaped [] context true
    [stmtId 0, stmtId 99] .unit (Core.LocalLoop.returned .unit) :=
  tree_of_lowerFlowStatements (fuel := 1) aligned (earlyUnique _)
    (earlyNoFor _ (by intros; simp)) (by rfl)

example : ∃ compiledFlow,
    Core.LocalControl.finish .unit (Core.LocalLoop.toControl .unit (Core.LocalLoop.returned .unit) escaped)
        (Core.LanguageResult.success .unit) =
      Core.LocalControl.finish .unit (Core.LocalLoop.toControl .unit compiledFlow escaped)
        (Core.LanguageResult.success .unit) ∧
    Tree compilation (earlySource (.returnStmt none)) reasonAt escaped [] context true [stmtId 0] .unit compiledFlow := by
  apply tree_of_lowerStatements (fuel := 1) (fellThroughReason := fellThrough) aligned (earlyUnique _)
    (earlyNoFor _ (by intros; simp))
  rfl

private def primitiveSource : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)]
  nodes := [expressionNode 0 .bool (.reference "flag" (.builtinBoolean true)),
    expressionNode 1 .bool (.unary .logicalNot (exprId 0)),
    statementNode 0 .unit (.whileLoop (exprId 1) [stmtId 1]),
    statementNode 1 .unit .breakStmt] }
private theorem primitiveNoFor : NoForLoops primitiveSource := by
  intro id node found initializer condition post body
  have member := (lookupStatement?_sound found).1
  simp [primitiveSource, expressionNode, statementNode] at member
  rcases member with rfl | rfl <;> simp

/-- Expression certificates come from the primitive policy, including unary
conditions; they are not assumed from a separate basic-expression tree. -/
example : Tree compilation primitiveSource reasonAt escaped [] context true [stmtId 0] .unit
    (Core.LocalLoop.sequence .unit
      (Core.LocalLoop.whileLoop .unit
        (Core.LocalPrimitiveResults.unary .boolNot (Core.LanguageResult.success (.bool true)))
        (Core.LocalLoop.breaking .unit) escaped)
      (Core.LocalLoop.fallthrough .unit)) := by
  apply tree_of_lowerFlowStatements (fuel := 5) aligned
    (show NodeOccurrencesUnique primitiveSource from by unfold NodeOccurrencesUnique nodeOccurrenceIds; decide)
    primitiveNoFor
  rfl

private def forSource : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)]
  nodes := [expressionNode 0 .bool (.reference "false" (.builtinBoolean false)),
    statementNode 0 .unit (.forLoop [] (exprId 0) [] [])] }

/-- For is supported by production lowering; this extraction excludes it by
an explicit static premise rather than a hidden assumed child certificate. -/
example : ¬NoForLoops forSource := by
  intro noFor
  exact noFor (id := stmtId 0) (node := {
    id := stmtId 0, span, type := .unit, form := .forLoop [] (exprId 0) [] [] })
    (by rfl) [] (exprId 0) [] [] rfl

example : SourceCoreLoops.lowerFlowStatementsWithPolicy (defaultPolicy compilation) 4 forSource []
    [stmtId 0] .unit reasonAt true escaped = .ok
      (Core.LocalLoop.sequence .unit
        (Core.LocalLoop.iterate .unit (Core.LanguageResult.success (.bool false))
          (Core.LocalLoop.fallthrough .unit) (Core.LocalLoop.fallthrough .unit) escaped)
        (Core.LocalLoop.fallthrough .unit)) := by rfl

end Tests.SourceCoreLoopStatementCertificates

import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBodyTree
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableLambdaViewBodyTree
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableLambdaViewEdits CallableLambdaBodyReachability GenericLexicalStatements

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"lambda_body_view", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "lambda_body_view.solc"⟩, 0, 1⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def boolean : ExpressionNode := {id := id 0, span, type := .bool, form := .reference "true" (.builtinBoolean true)}
private def returned : StatementNode := ⟨⟨⟨owner, 1⟩⟩, span, .bool, .returnStmt (some boolean.id)⟩
private def parent : ExpressionNode := {
  id := id 2, span, type := .function .unit .bool, form := .lambda [] .bool [returned.id]}
private def source : TypedSource := {
  owner, inputs := [], roots := [.expression parent.id], nodes := [.expression boolean, .statement returned, .expression parent]}
private def view := SourceCoreEvidence.withNode source {parent with type := .unit}
private def roots : List NodeId := [.statement returned.id]
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem edited : LocalView source view [parent.id] := withNode unique (by rfl) rfl rfl

private theorem reached_shape {node : NodeId} (reached : Reaches source roots node) :
    node = .statement returned.id ∨ node = .expression boolean.id := by
  induction reached with
  | root member => exact .inl (by simpa [roots] using member)
  | @expression expression node child parent found edge ih =>
    rcases ih with incompatible | equal
    · cases incompatible
    · have same : expression = boolean.id := NodeId.expression.inj equal
      subst expression
      have nodeEq : boolean = node := Option.some.inj ((show source.lookupExpression? boolean.id = some boolean from rfl).symm.trans found)
      subst node
      cases edge
  | @statement statement node child parent found edge ih =>
    rcases ih with equal | incompatible
    · have same : statement = returned.id := NodeId.statement.inj equal
      subst statement
      have nodeEq : returned = node := Option.some.inj ((show source.lookupStatement? returned.id = some returned from rfl).symm.trans found)
      subst node
      exact .inr (by simpa [returned, StatementForm.references] using edge)
    · cases incompatible

private theorem avoids : Avoids source roots [parent.id] := by
  intro expression member reached
  simp only [List.mem_singleton] at member
  subst expression
  rcases reached_shape reached with incompatible | equal
  · cases incompatible
  · cases equal

/-- The parent header really changes; the disjoint body proof retains the
literal's complete original metadata and the same generated return code. -/
theorem literal_body {layouts : SourceCoreAllocationLayouts.Prepared}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {values : ValuesContext} {context : SourceSemantics.Context} {scope : Scope} :
    source ≠ view ∧ Tree layouts ⟨owner, []⟩ [] frame globals onError values view
      (fun _ _ => CompatibleExpressionLiterals.Certificate [] view)
      context scope true [returned.id] .bool .bool (LocalLoop.returnValue .bool (LanguageResult.success (.bool true))) := by
  refine ⟨by decide, ?_⟩
  apply CallableLambdaViewBodyTree.literals (statements := [returned.id]) (solved := []) edited (by exact avoids)
  exact GenericLexicalStatements.Tree.returnValue (node := returned) (expressionNode := boolean)
    (lowered := ⟨.bool, LanguageResult.success (.bool true)⟩) [] (by rfl) rfl (by rfl) rfl
    ⟨boolean, rfl, .bool true rfl rfl rfl rfl⟩

private def literalPolicy : SourceCoreLoops.Policy := {
  lowerExpression := fun fuel source scope id reasonAt =>
    SourceCoreBasic.lowerExpression fuel source scope id (reasonAt id) }

/-- An accepted actual flow expression at the changed view yields the original
source's static Tree. The expression callback is the real basic literal path. -/
theorem accepted_original {layouts : SourceCoreAllocationLayouts.Prepared}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {values : ValuesContext} {context : SourceSemantics.Context} {code : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy literalPolicy 4 view []
      [returned.id] .bool (fun _ => Word.zero) true Word.zero = .ok code) :
    Tree layouts ⟨owner, []⟩ [] frame globals onError values source
      (fun _ _ => CompatibleExpressionLiterals.Certificate [] source)
      context [] true [returned.id] .bool .bool code := by
  have emitted : SourceCoreLoops.lowerFlowStatementsWithPolicy literalPolicy 4 view []
      [returned.id] .bool (fun _ => Word.zero) true Word.zero =
      .ok (LocalLoop.returnValue .bool (LanguageResult.success (.bool true))) := by rfl
  have same := Except.ok.inj (emitted.symm.trans accepted)
  cases same
  exact CallableLambdaViewBodyTree.literals_original edited (by exact avoids) literal_body.2

/-- A direct body reference to an edited parent violates the necessary
freshness premise. No tree/acyclicity assumption is silently added. -/
theorem parent_reference_forbidden {original : TypedSource} {bodyRoots : List NodeId}
    {changed : ExpressionId} {statement : StatementId} {node : StatementNode}
    (root : NodeId.statement statement ∈ bodyRoots)
    (found : original.lookupStatement? statement = some node)
    (edge : NodeId.expression changed ∈ node.form.references) :
    ¬Avoids original bodyRoots [changed] :=
  fun avoids => avoids changed (by simp) (.statement (.root root) found edge)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content :=
    "function make() returns (function() returns (Word)) { return lam() -> Word { let x: Word = 1; { 2; } if (true) { 3; } else { 4; } return 5; }; }"}] }

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "body view checker" (checkProgram workspace)
  let signature ← match program.signatures.functions.find? (·.name == "make") with
    | some signature => pure signature
    | none => throw (IO.userError "body view signature missing")
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 128 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"body view worklist {reprStr result}")
  let automatic ← SourceCompilerFeatureSupport.get "body view base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "body view indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let template ← match prepared.ancestry.templates.lambdas with
    | template :: _ => pure template
    | [] => throw (IO.userError "body view template missing")
  let statements ← match template.node.form with
    | .lambda [] _ statements => pure statements
    | _ => throw (IO.userError "body view zero-parameter lambda missing")
  let caller ← match plan.specializations.find? (fun caller => decide (caller.key = template.owner)) with
    | some caller => pure caller
    | none => throw (IO.userError "body view actual caller missing")
  let original := template.context.inventory.source
  let edited := SourceCoreEvidence.withNode original {template.node with type := .bool}
  let compilation : SourceCoreFunctions.Context := {
    plan, globals := automatic.prepared.globals, owner := template.owner, administrativePrefix := 1,
    solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero}
  let values := SourceCoreCompatibleValues.Context.initial automatic.checked
  let expressions := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
  let allocate := prepared.layouts.allocatorAt template.owner template.active (fun error => .sourceAllocation (reprStr error))
  let policy : SourceCoreLoops.Policy := {
    lowerExpression := fun fuel source scope id reason => SourceCoreFunctions.lowerExpressionWithPolicy expressions
      (fun _ _ _ _ _ _ _ _ _ => .ok .unit) fuel compilation source scope id reason
    readStatement := SourceCoreCompatibleDataExpressions.readStatement values.checked
    lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder values.checked
    sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.ancestry.layout.frame
      automatic.prepared.globals.length allocate)}
  let before ← SourceCompilerFeatureSupport.get "original lexical body"
    (SourceCoreLoops.lowerStatementsWithPolicy policy 300 original [] statements .word (fun _ => Word.zero) Word.zero Word.zero)
  let after ← SourceCompilerFeatureSupport.get "edited lexical body"
    (SourceCoreLoops.lowerStatementsWithPolicy policy 300 edited [] statements .word (fun _ => Word.zero) Word.zero Word.zero)
  SourceCompilerFeatureSupport.require (before == after) "parent header edit changed actual lexical body allocation/control code"
  SourceCompilerFeatureSupport.require
    (SourceCoreDataPlaces.declaredBinders original == SourceCoreDataPlaces.declaredBinders edited)
    "parent header edit changed original binder metadata"
  IO.println "lambda body views: disjoint literal Tree and actual let/block/if compiler code preserved GREEN"
end Tests.SourceCoreCallableLambdaViewBodyTree

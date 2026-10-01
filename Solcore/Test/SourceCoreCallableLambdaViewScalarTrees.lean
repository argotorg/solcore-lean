import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewScalarTrees
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableLambdaViewScalarTrees
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableLambdaViewEdits CallableLambdaBodyReachability

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"lambda_scalar_view", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "lambda_scalar_view.solc"⟩, 0, 1⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def boolean (index : Nat) (value : Bool) : ExpressionNode :=
  {id := id index, span, type := .bool, form := .reference "boolean" (.builtinBoolean value)}
private def negated : ExpressionNode := {id := id 2, span, type := .bool, form := .unary .logicalNot (id 0)}
private def binary : ExpressionNode := {id := id 3, span, type := .bool, form := .binary (id 2) .logicalOr (id 1)}
private def conditional : ExpressionNode := {id := id 4, span, type := .bool, form := .conditional (id 3) (id 0) (id 1)}
private def grouped : ExpressionNode := {id := id 5, span, type := .bool, form := .group (id 4)}
private def paired : ExpressionNode := {id := id 6, span, type := .product .bool .bool, form := .tuple [id 5, id 1]}
private def parent : ExpressionNode := {id := id 7, span, type := .function .unit .bool, form := .lambda [] .bool []}
private def source : TypedSource := {owner, inputs := [], roots := [.expression parent.id], nodes :=
  [.expression (boolean 0 true), .expression (boolean 1 false), .expression negated,
    .expression binary, .expression conditional, .expression grouped, .expression paired, .expression parent]}
private def view := SourceCoreEvidence.withNode source {parent with type := .unit}
private def roots : List NodeId := [.expression paired.id]
private def footprint : List NodeId := ([0, 1, 2, 3, 4, 5, 6] : List Nat).map (fun n => .expression (id n))
private theorem edited : LocalView source view [parent.id] :=
  withNode (by cbv; decide) (by rfl) rfl rfl

private theorem reference_closed {expression : ExpressionId} {node : ExpressionNode}
    (member : NodeId.expression expression ∈ footprint) (found : source.lookupExpression? expression = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : child ∈ footprint := by
  simp only [footprint, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false, NodeId.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have selected := Option.some.inj ((by rfl : source.lookupExpression? _ = some _).symm.trans found)
    subst node
    simp only [boolean, negated, binary, conditional, grouped, paired, ExpressionForm.references,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at edge <;>
      rcases edge with rfl | rfl | rfl <;> simp [footprint, id]

private theorem reached_member {node : NodeId} (reached : Reaches source roots node) : node ∈ footprint := by
  induction reached with
  | @root rootId member =>
    have same : rootId = NodeId.expression paired.id := by simpa [roots] using member
    rw [same]
    simp [footprint, paired, id]
  | expression _ found edge ih => exact reference_closed ih found edge
  | statement _ _ _ ih => simp [footprint] at ih

private theorem avoids : Avoids source roots [parent.id] := by
  intro expression member reached
  simp only [List.mem_singleton] at member
  subst expression
  have impossible := reached_member reached
  simp [parent, footprint, id] at impossible

private def unaryCode := LocalPrimitiveResults.unary .boolNot (LanguageResult.success (.bool true))
private def binaryCode := SourceCorePrimitive.binary .logicalOr unaryCode (LanguageResult.success (.bool false))
private def conditionalCode := LocalControl.choose .bool binaryCode
  (LanguageResult.success (.bool true)) (LanguageResult.success (.bool false))
private def code : SourceCoreBasic.LoweredExpr :=
  ⟨.product .bool .bool, LocalSequence.pair .bool .bool conditionalCode (LanguageResult.success (.bool false))⟩

private theorem originalTree {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context} :
    CompatibleExpressionConditionals.Tree 10 values source context [] (fun _ => Word.zero) [] paired.id code := by
  apply CompatibleExpressionConditionals.Tree.pair (node := paired) (leftNode := grouped)
    (rightNode := boolean 1 false) (first := ⟨.bool, conditionalCode⟩) (second := ⟨.bool, LanguageResult.success (.bool false)⟩)
    ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
  · apply CompatibleExpressionConditionals.Tree.group (node := grouped) (innerNode := conditional)
      ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl
    apply CompatibleExpressionConditionals.Tree.conditional (node := conditional)
      (conditionNode := binary) (thenNode := boolean 0 true) (elseNode := boolean 1 false)
      ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl rfl rfl
    · apply CompatibleExpressionConditionals.Tree.primitive
      apply CompatibleExpressionPrimitives.Tree.binary (node := binary) (leftNode := negated)
        (rightNode := boolean 1 false) (mode := .word)
        ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl rfl .logicalOr
      · apply CompatibleExpressionPrimitives.Tree.unary (node := negated) (childNode := boolean 0 true)
          ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl .logicalNot
        exact .product (.literal ⟨boolean 0 true, rfl, .bool true rfl rfl rfl rfl⟩)
      · exact .product (.literal ⟨boolean 1 false, rfl, .bool false rfl rfl rfl rfl⟩)
    · exact .primitive (.product (.literal ⟨boolean 0 true, rfl, .bool true rfl rfl rfl rfl⟩))
    · exact .primitive (.product (.literal ⟨boolean 1 false, rfl, .bool false rfl rfl rfl rfl⟩))
  · exact .primitive (.product (.literal ⟨boolean 1 false, rfl, .bool false rfl rfl rfl rfl⟩))

/-- Real operator profiles and all three conditional children survive the
changed parent header. The complete sources remain different. -/
theorem scalar_view {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context} :
    source ≠ view ∧ CompatibleExpressionConditionals.Tree 10 values view context []
      (fun _ => Word.zero) [] paired.id code :=
  ⟨by decide, CallableLambdaViewScalarTrees.conditionals edited avoids originalTree (.root (by simp [roots]))⟩

theorem scalar_original {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
    (tree : CompatibleExpressionConditionals.Tree 10 values view context [] (fun _ => Word.zero) [] paired.id code) :
    CompatibleExpressionConditionals.Tree 10 values source context [] (fun _ => Word.zero) [] paired.id code :=
  CallableLambdaViewScalarTrees.conditionals_original edited avoids tree (.root (by simp [roots]))

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content :=
    "function make(seed: Word) returns (function() returns (Word)) { return lam() -> Word { let table: mapping(Word => Word); let missing: Word; @Word; false ? missing : table[1]; return ((!false && true) ? (seed + 2) : (seed * 3)); }; }"}] }

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "scalar view checker" (checkProgram workspace)
  let signature ← match program.signatures.functions.find? (·.name == "make") with
    | some signature => pure signature
    | none => throw (IO.userError "scalar view signature missing")
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 128 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"scalar view worklist {reprStr result}")
  let automatic ← SourceCompilerFeatureSupport.get "scalar view base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "scalar view indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let template ← match prepared.ancestry.templates.lambdas with
    | template :: _ => pure template
    | [] => throw (IO.userError "scalar view template missing")
  let statements ← match template.node.form with
    | .lambda [] _ statements => pure statements
    | _ => throw (IO.userError "scalar view lambda missing")
  let caller ← match plan.specializations.find? (fun caller => decide (caller.key = template.owner)) with
    | some caller => pure caller
    | none => throw (IO.userError "scalar view caller missing")
  let original := template.context.inventory.source
  let modified := SourceCoreEvidence.withNode original {template.node with type := .bool}
  let compilation : SourceCoreFunctions.Context := {
    plan, globals := automatic.prepared.globals, owner := template.owner, administrativePrefix := 1,
    solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero}
  let values := SourceCoreCompatibleValues.Context.initial automatic.checked
  let expressions := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
  let mut scope : SourceCoreLocalCell.Scope := []
  for binder in SourceCoreDataPlaces.declaredBinders original do
    match values.checked.catalog.project binder.scheme.body with
    | .ok type => scope := (binder.id, type) :: scope
    | .error _ => pure ()
  let mut acceptedCount := 0
  let mut reads := 0
  let mut choices := 0
  let mut proxies := 0
  for node in original.nodes do
    match node with
    | .expression node =>
      if node.id != template.node.id then
        let before := SourceCoreFunctions.lowerExpressionWithPolicy expressions
          (fun _ _ _ _ _ _ _ _ _ => .ok .unit) 100 compilation original scope node.id (fun _ => Word.zero)
        let after := SourceCoreFunctions.lowerExpressionWithPolicy expressions
          (fun _ _ _ _ _ _ _ _ _ => .ok .unit) 100 compilation modified scope node.id (fun _ => Word.zero)
        SourceCompilerFeatureSupport.require (reprStr before == reprStr after) "view changed actual scalar lowering or diagnostic"
        match before with
        | .ok _ =>
          acceptedCount := acceptedCount + 1
          match node.form with
          | .reference _ (.local _) => reads := reads + 1
          | .conditional _ _ _ => choices := choices + 1
          | .proxy _ => proxies := proxies + 1
          | _ => pure ()
        | .error _ => pure ()
    | .statement _ => pure ()
  SourceCompilerFeatureSupport.require (!statements.isEmpty) "scalar view body missing"
  SourceCompilerFeatureSupport.require (acceptedCount ≥ 10 && reads ≥ 3 && choices ≥ 2 && proxies ≥ 1)
    "scalar view regression did not exercise accepted reads, choices and proxy"
  IO.println "lambda scalar views: static compound tree, raw read metadata and actual lowering equality GREEN"
end Tests.SourceCoreCallableLambdaViewScalarTrees

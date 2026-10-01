import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSourceTyping
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCallableLambdaViewSourceTyping
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableLambdaViewEdits CallableLambdaBodyReachability CompatibleExpressionBuiltins

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"lambda_view_source_typing", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "lambda_view_source_typing.solc"⟩, 0, 1⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def literalNode : ExpressionNode := {
  id := id 0, span, type := .word, form := .literal (.decimal "7")}
private def toNode : ExpressionNode := {
  id := id 1, span, type := BuiltinFunctionId.wordToInteger.type,
  form := .reference "wordToInteger" (.builtinFunction .wordToInteger)}
private def innerNode : ExpressionNode := {
  id := id 2, span, type := .integer, form := .call (id 1) [id 0] (.builtinFunction .wordToInteger)}
private def fromNode : ExpressionNode := {
  id := id 3, span, type := BuiltinFunctionId.wordFromInteger.type,
  form := .reference "wordFromInteger" (.builtinFunction .wordFromInteger)}
private def outerNode : ExpressionNode := {
  id := id 4, span, type := .word, form := .call (id 3) [id 2] (.builtinFunction .wordFromInteger)}
private def groupNode : ExpressionNode := {id := id 5, span, type := .word, form := .group (id 4)}
private def boolean : ExpressionNode := {id := id 7, span, type := .bool, form := .reference "true" (.builtinBoolean true)}
private def discarded : StatementNode := ⟨⟨⟨owner, 10⟩⟩, span, .unit, .expression (id 5) true⟩
private def block : StatementNode := ⟨⟨⟨owner, 11⟩⟩, span, .unit, .block [discarded.id]⟩
private def returned : StatementNode := ⟨⟨⟨owner, 12⟩⟩, span, .word, .returnStmt (some (id 5))⟩
private def conditional : StatementNode := ⟨⟨⟨owner, 13⟩⟩, span, .unit, .ifThen boolean.id [returned.id] (some [returned.id])⟩
private def body : List StatementId := [block.id, conditional.id, returned.id]
private def parent : ExpressionNode := {id := id 6, span, type := .function .unit .word, form := .lambda [] .word body}
private def source : TypedSource := {
  owner, inputs := [], roots := body.map NodeId.statement, nodes := [.expression literalNode, .expression toNode,
    .expression innerNode, .expression fromNode, .expression outerNode, .expression groupNode, .expression boolean, .statement discarded, .statement block, .statement returned, .statement conditional, .expression parent]}
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem wordAdmitted : TypeAdmissible context .word := .word (.ofSignatures signatures)
private theorem integerAdmitted : TypeAdmissible context .integer := .integer (.ofSignatures signatures)
private theorem literalTyped : ExpressionHasType source context (id 0) .word := by
  apply ExpressionHasType.ofOrdinary (node := literalNode) (rawType := .word) (lookupExpression?_sound (by rfl))
    (.literal (.intro (numericLiteralValue?_sound (value := 7) (by rfl)))) wordAdmitted wordAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem innerTyped : ExpressionHasType source context (id 2) .integer := by
  apply ExpressionHasType.ofOrdinary (node := innerNode) (rawType := .integer) (lookupExpression?_sound (by cbv))
    (.builtinCall (.intro (lookupExpression?_sound (node := toNode) (by cbv)) rfl rfl rfl rfl)
      (.cons literalTyped (.nil _))) integerAdmitted integerAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem outerTyped : ExpressionHasType source context (id 4) .word := by
  apply ExpressionHasType.ofOrdinary (node := outerNode) (rawType := .word) (lookupExpression?_sound (by cbv))
    (.builtinCall (.intro (lookupExpression?_sound (node := fromNode) (by cbv)) rfl rfl rfl rfl)
      (.cons innerTyped (.nil _))) wordAdmitted wordAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem groupTyped : ExpressionHasType source context (id 5) .word := by
  apply ExpressionHasType.ofOrdinary (node := groupNode) (rawType := .word) (lookupExpression?_sound (by cbv))
    (.group outerTyped) wordAdmitted wordAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem literalSyntax : CompatibleExpressionGeneral.Syntax source (id 0) :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := literalNode) (by rfl) (.word _)))))))
private theorem innerSyntax : Syntax source (id 2) :=
  .builtin (node := innerNode) (by cbv) rfl (by intro child member; simp only [List.mem_singleton] at member; subst child; exact .fragment literalSyntax)
private theorem outerSyntax : Syntax source (id 4) :=
  .builtin (node := outerNode) (by cbv) rfl (by intro child member; simp only [List.mem_singleton] at member; subst child; exact innerSyntax)
private theorem syntaxTree : Syntax source (id 5) := .group (node := groupNode) (by cbv) rfl outerSyntax

private theorem booleanTyped : ExpressionHasType source context boolean.id .bool := by
  apply ExpressionHasType.ofOrdinary (node := boolean) (rawType := .bool) (lookupExpression?_sound (by cbv))
    (.reference (.builtinBoolean true)) (.bool (.ofSignatures signatures)) (.bool (.ofSignatures signatures))
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem booleanSyntax : CompatibleExpressionBuiltins.Syntax source boolean.id :=
  .fragment (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := boolean) (by cbv) (.bool _ true))))))))
private theorem returnSyntax (mode : Bool) : BuiltinLexicalStatements.Syntax source context mode [returned.id] .word :=
  .returnValue (node := returned) [] (by cbv) rfl rfl (by cbv) rfl groupTyped syntaxTree
private theorem bodySyntax : BuiltinLexicalStatements.Syntax source context true body .word := by
  apply GenericLexicalStatements.Syntax.block (node := block) (by cbv) rfl rfl
  · exact .discard (node := discarded) (expressionNode := groupNode) (by cbv) rfl rfl rfl (by cbv)
      groupTyped syntaxTree (.nil (.inl rfl))
  · exact .ifThen (node := conditional) (conditionNode := boolean) (by cbv) rfl rfl (by cbv) rfl
      booleanTyped booleanSyntax (returnSyntax false) (returnSyntax false) (returnSyntax true)
private def view := SourceCoreEvidence.withNode source {parent with type := .unit}
private def footprint : List NodeId :=
  [.expression (id 0), .expression (id 1), .expression (id 2), .expression (id 3), .expression (id 4),
    .expression (id 5), .expression (id 7), .statement discarded.id, .statement block.id, .statement returned.id, .statement conditional.id]
private theorem edited : LocalView source view [parent.id] := withNode unique (by cbv) rfl rfl
private theorem expression_closed {expression : ExpressionId} {node : ExpressionNode}
    (member : NodeId.expression expression ∈ footprint) (found : source.lookupExpression? expression = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : child ∈ footprint := by
  simp [footprint] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have selected := Option.some.inj ((by rfl : source.lookupExpression? _ = some _).symm.trans found)
    subst node
    simp only [literalNode, toNode, innerNode, fromNode, outerNode, groupNode, boolean,
      ExpressionForm.references, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at edge <;>
      rcases edge with rfl | rfl <;> simp [footprint, id]
private theorem statement_closed {statement : StatementId} {node : StatementNode}
    (member : NodeId.statement statement ∈ footprint) (found : source.lookupStatement? statement = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : child ∈ footprint := by
  simp [footprint] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals
    have selected := Option.some.inj ((by rfl : source.lookupStatement? _ = some _).symm.trans found)
    subst node
    simp [discarded, block, returned, conditional, StatementForm.references] at edge <;>
      rcases edge with rfl | rfl | rfl <;> simp [footprint, id, discarded, block, returned, conditional, boolean]
private theorem reached_member {node : NodeId}
    (reached : Reaches source (body.map NodeId.statement) node) : node ∈ footprint := by
  induction reached with
  | root member =>
    simp only [body, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [footprint]
  | expression _ found edge ih => exact expression_closed ih found edge
  | statement _ found edge ih => exact statement_closed ih found edge
private theorem avoids : Avoids source (body.map NodeId.statement) [parent.id] := by
  intro expression member reached
  simp only [List.mem_singleton] at member
  subst expression
  have impossible := reached_member reached
  simp [footprint, parent, id] at impossible
private theorem groupReached : Reaches source (body.map NodeId.statement) (.expression groupNode.id) :=
  .statement (.root (by simp [body])) (by cbv : source.lookupStatement? returned.id = some returned)
    (by simp [returned, StatementForm.references, groupNode])

/-- The enclosing header really changes while independent nested builtin
source typing retains the exact Word result and all original metadata. -/
theorem independent_nested_view : source ≠ view ∧ ExpressionHasType view context groupNode.id .word :=
  ⟨by decide, CallableLambdaViewSourceTyping.expression_typing edited avoids unique syntaxTree groupReached groupTyped⟩

/-- Canonical typing is recovered from actual view typing, with no canonical
compiler success or source execution supplied to the transport. -/
theorem independent_nested_original : ExpressionHasType source context groupNode.id .word :=
  CallableLambdaViewSourceTyping.expression_typing_original edited avoids unique
    (CallableLambdaViewSourceTyping.expression_syntax edited avoids unique syntaxTree groupReached)
    groupReached independent_nested_view.2

theorem lexical_view : BuiltinLexicalStatements.Syntax view context true body .word :=
  CallableLambdaViewSourceTyping.body_syntax edited avoids unique bodySyntax

theorem lexical_original : BuiltinLexicalStatements.Syntax source context true body .word :=
  CallableLambdaViewSourceTyping.body_syntax_original edited avoids unique lexical_view

/-- Even a builtin callee has an actual reachability edge. Excluding only the
argument expression syntax is insufficient for this source-typing theorem. -/
theorem changed_callee_rejected : ¬Avoids source (body.map NodeId.statement) [toNode.id] := by
  intro fresh
  have outerReached : Reaches source (body.map NodeId.statement) (.expression outerNode.id) :=
    .expression (node := groupNode) groupReached (by cbv) (by simp [groupNode, ExpressionForm.references, outerNode, id])
  have innerReached : Reaches source (body.map NodeId.statement) (.expression innerNode.id) :=
    .expression (node := outerNode) outerReached (by cbv) (by simp [outerNode, ExpressionForm.references, innerNode, id])
  have calleeReached : Reaches source (body.map NodeId.statement) (.expression toNode.id) :=
    .expression (node := innerNode) innerReached (by cbv) (by simp [innerNode, ExpressionForm.references, toNode, id])
  exact fresh toNode.id (by simp) calleeReached

/-- A metadata view alone permits changed output metadata at a reached parent.
The freshness hypothesis is therefore a real source boundary. -/
theorem parent_reached_rejected : ¬Avoids source [.expression parent.id] [parent.id] :=
  fun fresh => fresh parent.id (by simp) (.root (by simp))

private def changedChild := SourceCoreEvidence.withNode source {groupNode with type := .bool}
private theorem childEdited : LocalView source changedChild [groupNode.id] :=
  withNode unique (by cbv) rfl rfl

/-- Preserved owner/forms/statement metadata cannot establish the original
source type at an edited, reached expression. Complete lookup equality is
strictly stronger than that metadata relation. -/
theorem metadata_alone_insufficient :
    LambdaMetadataViews.MetadataView source changedChild ∧
      ¬ExpressionHasType changedChild context groupNode.id .word := by
  refine ⟨childEdited.metadata, ?_⟩
  intro typed
  obtain ⟨selected, rawType, contains, output, _⟩ := typed.raw_type_and_output_path
  have found : changedChild.lookupExpression? groupNode.id = some {groupNode with type := .bool} := by rfl
  have same := Option.some.inj ((lookupExpression?_complete (childEdited.metadata.unique unique) contains).symm.trans found)
  subst selected
  cases output

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function nested() returns (integer) { let f: function() returns (integer) = lam() -> integer { let x: Word = 7; { integerEq(wordToInteger(x), wordToInteger(x)); } if (integerLt(wordToInteger(x), wordToInteger(x))) { return wordToInteger(x); } else { x; } return integerSub(wordToInteger(x), wordToInteger(3)); }; return 0; }",
    "function indexed() returns (integer) { let f: function() returns (Word) = lam() -> Word { let table: mapping((Bool, Bool) => Word); let spare: Word; { @Word; } if (integerEq(wordToInteger(2), wordToInteger(2))) { 3; } else { 4; } return table[(integerEq(wordToInteger(2), wordToInteger(2)), integerLt(wordToInteger(2), wordToInteger(2)))]; }; return 0; }",
    "function branch() returns (integer) { let f: function() returns (Bool) = lam() -> Bool { let x: Word = 3; if (integerEq(wordToInteger(x), wordToInteger(x))) { let y: Word = 7; y; } else { let y: Word; y; } return integerLt(wordToInteger(x), integerSub(wordToInteger(x), wordToInteger(1))); }; return 0; }"]}] }

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "source typing checker" (checkProgram workspace)
  let seeds := program.signatures.functions.map fun signature => ⟨signature.id, []⟩
  let plan ← match SourceSpecializationWorklist.run program seeds 128 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"source typing worklist {reprStr result}")
  let base ← SourceCompilerFeatureSupport.get "source typing base" (SourceCoreCompatibleFunctions.prepare program plan 800)
  let prepared ← SourceCompilerFeatureSupport.get "source typing indexed" (SourceCoreCallableIndexedPrograms.prepare base.prepared 800)
  let native ← match base.prepared.callableContext with
    | some native => pure native | none => throw (IO.userError "source typing actual callable context missing")
  let mut bodies := 0
  for template in prepared.ancestry.templates.lambdas do
    let statements ← match template.node.form with
      | .lambda [] _ body => pure body | _ => throw (IO.userError "source typing lambda shape")
    let original := template.context.inventory.source
    let modified := SourceCoreEvidence.withNode original {template.node with type := .unit}
    let caller ← match plan.specializations.find? (fun caller => decide (caller.key = template.owner)) with
      | some caller => pure caller | none => throw (IO.userError "source typing caller missing")
    let compilation : SourceCoreFunctions.Context := {
      plan, globals := base.prepared.globals, owner := template.owner, administrativePrefix := 1,
      solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero}
    let values := SourceCoreCompatibleValues.Context.initial base.checked
    let expressions : SourceCoreFunctions.Policy :=
      {SourceCoreCompatibleDataExpressions.functionPolicy 100 values with
        callables := SourceCoreGeneralFunctions.callablePolicy (some native) []}
    let allocate := prepared.layouts.allocatorAt template.owner template.active (fun error => .sourceAllocation (reprStr error))
    let policy : SourceCoreLoops.Policy := {
      lowerExpression := fun fuel source scope id reason => SourceCoreFunctions.lowerExpressionWithPolicy expressions
        (fun _ _ _ _ _ _ _ _ _ => .ok .unit) fuel compilation source scope id reason
      readStatement := SourceCoreCompatibleDataExpressions.readStatement values.checked
      lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder values.checked
      sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.ancestry.layout.frame
        base.prepared.globals.length allocate)}
    let before ← SourceCompilerFeatureSupport.get "source typing canonical body"
      (SourceCoreLoops.lowerStatementsWithPolicy policy 400 original [] statements template.resultType
        (fun _ => Word.zero) Word.zero Word.zero)
    let after ← SourceCompilerFeatureSupport.get "source typing actual view body"
      (SourceCoreLoops.lowerStatementsWithPolicy policy 400 modified [] statements template.resultType
        (fun _ => Word.zero) Word.zero Word.zero)
    SourceCompilerFeatureSupport.require (original != modified) "source typing header did not change"
    SourceCompilerFeatureSupport.require (before == after) "source typing view changed ordinary lexical/builtin code"
    SourceCompilerFeatureSupport.require (SourceCoreDataPlaces.declaredBinders original == SourceCoreDataPlaces.declaredBinders modified)
      "source typing view changed exact local declarations"
    bodies := bodies + 1
  SourceCompilerFeatureSupport.require (bodies == 3) "source typing did not inspect all checked lambda bodies"
  IO.println "lambda source typing: independent nested builtin/lexical transport, changed-callee rejection, actual three body receipts GREEN"
end Tests.SourceCoreCallableLambdaViewSourceTyping

import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewStaticTyping
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCallableLambdaViewStaticTyping
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableLambdaViewEdits CallableLambdaBodyReachability

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"lambda_full_static", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "lambda_full_static.solc"⟩, 0, 1⟩
private def eid (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def sid (index : Nat) : StatementId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private def control : ControlContext := ⟨.word, 0⟩
private def word : ExpressionNode := {id := eid 0, span, type := .word, form := .literal (.decimal "7")}
private def boolean : ExpressionNode := {id := eid 1, span, type := .bool, form := .reference "false" (.builtinBoolean false)}
private def returned : StatementNode := {id := sid 10, span, type := .word, form := .returnStmt (some word.id)}
private def lambda : ExpressionNode := {id := eid 2, span, type := .function .unit .word, form := .lambda [] .word [returned.id]}
private def indirect : IndirectCallResolution := ⟨0, .unit, .unit, []⟩
private def called : ExpressionNode := {id := eid 3, span, type := .word, form := .call lambda.id [] (.indirect indirect)}
private def discarded : StatementNode := {id := sid 11, span, type := .unit, form := .expression called.id true}
private def breaking : StatementNode := {id := sid 12, span, type := .unit, form := .breakStmt}
private def continuing : StatementNode := {id := sid 13, span, type := .unit, form := .continueStmt}
private def whileNode : StatementNode := {id := sid 14, span, type := .unit, form := .whileLoop boolean.id [breaking.id]}
private def forNode : StatementNode := {
  id := sid 15
  span
  type := .unit
  form := .forLoop [.expression called.id] boolean.id [.expression word.id] [continuing.id]}
private def arm : TypedMatchCase := ⟨span, ⟨.wildcard span span, .word, .wildcard, []⟩, [returned.id]⟩
private def resolution : MatchResolution := ⟨word.id, ⟨owner, 0⟩, [arm], some [returned.id], []⟩
private def matched : StatementNode := {id := sid 16, span, type := .word, form := .matchWith resolution}
private def body : List StatementId := [discarded.id, whileNode.id, forNode.id, matched.id, returned.id]
private def cycle : ExpressionNode := {id := eid 98, span, type := .word, form := .group (eid 98)}
private def outer : ExpressionNode := {id := eid 99, span, type := .function .unit .word, form := .lambda [] .word body}
private def source : TypedSource := {
  owner
  inputs := []
  roots := body.map NodeId.statement
  nodes := [.expression word, .expression boolean, .expression lambda, .expression called,
    .statement returned, .statement discarded, .statement breaking, .statement continuing,
    .statement whileNode, .statement forNode, .statement matched, .expression cycle, .expression outer]}
private def view : TypedSource := SourceCoreEvidence.withNode source {outer with type := .bool}
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem edited : LocalView source view [outer.id] := withNode unique (by rfl) rfl rfl
private theorem wordAdmissible : TypeAdmissible context .word := .word (.ofSignatures signatures)
private theorem wordTyped : ExpressionHasType source context word.id .word := by
  apply ExpressionHasType.ofOrdinary (node := word) (rawType := .word) (lookupExpression?_sound (by rfl))
    (.literal (.intro (numericLiteralValue?_sound (value := 7) (by rfl)))) wordAdmissible wordAdmissible
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem boolTyped : ExpressionHasType source context boolean.id .bool := by
  apply ExpressionHasType.ofOrdinary (node := boolean) (rawType := .bool) (lookupExpression?_sound (by rfl))
    (.reference (.builtinBoolean false)) (.bool (.ofSignatures signatures)) (.bool (.ofSignatures signatures))
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private def returnedFacts : StatementFacts := ⟨.word, true, true, .returned⟩
private def emptyFacts : StatementFacts := ⟨.unit, false, false, .ordinary .unit⟩
private def breakFacts : StatementFacts := ⟨.unit, false, false, .breaking⟩
private def continueFacts : StatementFacts := ⟨.unit, false, false, .continuing⟩
private theorem returnedTyped : StatementHasType source control context returned.id context returnedFacts :=
  .returnValue (lookupStatement?_sound (node := returned) (by rfl)) rfl wordTyped rfl
private theorem lambdaTyped : ExpressionHasType source context lambda.id (.function .unit .word) := by
  have admitted : TypeAdmissible context (.function .unit .word) :=
    .function (.unit (.ofSignatures signatures)) wordAdmissible
  apply ExpressionHasType.ofOrdinary (node := lambda) (rawType := .function .unit .word) (lookupExpression?_sound (by rfl))
    (.lambda (by simp) (.nil _) (.singleton returnedTyped) (by unfold BodyCompletes; decide)) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem calledTyped : ExpressionHasType source context called.id .word :=
  .intro (lookupExpression?_sound (node := called) (by rfl))
    (.indirectCall lambdaTyped (.nil _) (.intro rfl rfl rfl (.nil _))) rfl
    wordAdmissible wordAdmissible (.indirectCall (by intro id member; cases member) (.nil _) rfl)
private theorem discardedTyped : StatementHasType source control context discarded.id context emptyFacts :=
  .expressionDiscard (lookupStatement?_sound (node := discarded) (by rfl)) rfl calledTyped rfl
private theorem breakingTyped : StatementHasType source control.enterLoop context breaking.id context breakFacts :=
  .breakStmt (lookupStatement?_sound (node := breaking) (by rfl)) rfl (by change 0 < 1; decide) rfl
private theorem continuingTyped : StatementHasType source control.enterLoop context continuing.id context continueFacts :=
  .continueStmt (lookupStatement?_sound (node := continuing) (by rfl)) rfl (by change 0 < 1; decide) rfl
private def whileFacts : StatementFacts := ⟨.unit, false, false, .loop .breaking⟩
private def forFacts : StatementFacts := ⟨.unit, false, false, .loop .continuing⟩
private theorem whileTyped : StatementHasType source control context whileNode.id context whileFacts :=
  .whileLoop (lookupStatement?_sound (node := whileNode) (by rfl)) rfl boolTyped (.singleton breakingTyped) rfl
private theorem forTyped : StatementHasType source control context forNode.id context forFacts :=
  .forLoop (lookupStatement?_sound (node := forNode) (by rfl)) rfl
    (.cons (.expression calledTyped) (.nil _ _)) boolTyped (.singleton continuingTyped)
    (.cons (.expression wordTyped) (.nil _ _)) rfl
private theorem patternTyped : TypedMatchPatternHasType context arm.pattern .word [] 0 :=
  ⟨rfl, .wildcard, .wildcard, ⟨by simp, by simp⟩⟩
private theorem armTyped : MatchCaseHasType source control context .word arm (.singleton returnedFacts) :=
  .intro patternTyped (.nil _) (.singleton returnedTyped)
private theorem matchTyped : StatementHasType source control context matched.id context returnedFacts := by
  exact .matchWithDefault (show ContainsStatement source matched.id matched from lookupStatement?_sound (by rfl)) rfl rfl wordTyped
    (.cons armTyped (.nil _ _ _)) (.singleton returnedTyped) rfl (by rfl) rfl
private def bodyFacts : BodyFacts := .cons emptyFacts (.cons whileFacts (.cons forFacts
  (.cons returnedFacts (.singleton returnedFacts))))
private theorem bodyTyped : StatementsHaveType source control context body context bodyFacts :=
  .cons discardedTyped (.cons whileTyped (.cons forTyped (.cons matchTyped (.singleton returnedTyped))))

private def footprint : List NodeId := [.expression word.id, .expression boolean.id, .expression lambda.id, .expression called.id,
  .statement returned.id, .statement discarded.id, .statement breaking.id, .statement continuing.id,
  .statement whileNode.id, .statement forNode.id, .statement matched.id]
private theorem expression_closed {id : ExpressionId} {node : ExpressionNode}
    (member : NodeId.expression id ∈ footprint) (found : source.lookupExpression? id = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : child ∈ footprint := by
  simp [footprint] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals
    have same := Option.some.inj ((by rfl : source.lookupExpression? _ = some _).symm.trans found)
    subst node
    simp [word, boolean, lambda, called, ExpressionForm.references] at edge <;>
      subst child <;> simp [footprint, lambda, returned]
private theorem statement_closed {id : StatementId} {node : StatementNode}
    (member : NodeId.statement id ∈ footprint) (found : source.lookupStatement? id = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : child ∈ footprint := by
  simp [footprint] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have same := Option.some.inj ((by rfl : source.lookupStatement? _ = some _).symm.trans found)
    subst node
    simp [returned, discarded, breaking, continuing, whileNode, forNode, matched, resolution, arm,
      StatementForm.references, MatchResolution.references, TypedMatchCase.references, ForItemForm.references] at edge <;>
      rcases edge with rfl | rfl | rfl | rfl <;> simp [footprint, returned, continuing, breaking]
private theorem reached_member {id : NodeId} (reached : Reaches source (body.map NodeId.statement) id) : id ∈ footprint := by
  induction reached with
  | root member =>
    simp [body] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [footprint]
  | expression _ found edge ih => exact expression_closed ih found edge
  | statement _ found edge ih => exact statement_closed ih found edge
private theorem avoids : Avoids source (body.map NodeId.statement) [outer.id] := by
  intro id member reached
  simp only [List.mem_singleton] at member
  subst id
  have impossible := reached_member reached
  simp [footprint, outer, word, boolean, lambda, called, eid] at impossible
private theorem calledReached : Reaches source (body.map NodeId.statement) (.expression called.id) :=
  .statement (.root (by simp [body])) (by rfl : source.lookupStatement? discarded.id = some discarded)
    (by simp [discarded, StatementForm.references])

/-- The occurrence table contains an actual cycle outside the retained body;
the transport does not assume a global acyclic source graph. -/
theorem unrelated_cycle : source.lookupExpression? cycle.id = some cycle ∧
    NodeId.expression cycle.id ∈ cycle.form.references := by
  exact ⟨rfl, by simp [cycle, ExpressionForm.references]⟩

/-- This body contains an indirect lambda call, while/break, for/continue and
match. No expression Syntax or static lowering Tree appears in the transport. -/
theorem full_body : source ≠ view ∧ StatementsHaveType view control context body context bodyFacts :=
  ⟨by decide, (CallableLambdaViewStaticTyping.body_iff edited avoids unique).mp bodyTyped⟩

theorem full_body_original : StatementsHaveType source control context body context bodyFacts :=
  (CallableLambdaViewStaticTyping.body_iff edited avoids unique).mpr full_body.2

theorem nested_lambda_call : ExpressionHasType view context called.id .word :=
  CallableLambdaViewStaticTyping.expression edited avoids unique calledTyped calledReached

theorem nested_lambda_call_original : ExpressionHasType source context called.id .word :=
  CallableLambdaViewStaticTyping.expression_original edited avoids unique nested_lambda_call calledReached

/-- The lambda body is part of the actual reference closure; changing its
returned expression is rejected even when the outer occurrence is unchanged. -/
theorem reached_lambda_body_rejected : ¬Avoids source (body.map NodeId.statement) [word.id] := by
  intro fresh
  have lambdaReached : Reaches source (body.map NodeId.statement) (.expression lambda.id) :=
    .expression calledReached (by rfl : source.lookupExpression? called.id = some called)
      (by simp [called, ExpressionForm.references])
  have returnReached : Reaches source (body.map NodeId.statement) (.statement returned.id) :=
    .expression lambdaReached (by rfl : source.lookupExpression? lambda.id = some lambda)
      (by simp [lambda, ExpressionForm.references])
  exact fresh word.id (by simp) (.statement returnReached (by rfl : source.lookupStatement? returned.id = some returned)
    (by simp [returned, StatementForm.references]))

/- Direct callee metadata and indexed assignment keys are transported under
source-static premises, retaining the exact instantiation and requirement plan. -/
theorem direct_call {canonical changedSource : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (localView : LocalView canonical changedSource changed) (fresh : Avoids canonical roots changed)
    (unique : NodeOccurrencesUnique canonical) {context : SourceSemantics.Context}
    {callee : ExpressionId} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    {parameters : List TypeSystem.Ty} {result : TypeSystem.Ty} {predicates : List ProgramPredicate}
    (calleeTyped : DirectDeclarationCalleeValid context canonical callee instantiation)
    (application : DeclarationApplicationValid context instantiation parameters result predicates)
    (argumentTypes : ExpressionsHaveTypes canonical context arguments parameters)
    (reached : CallableLambdaViewStaticTyping.Within canonical roots
      (ExpressionForm.call callee arguments (.declaration instantiation)).references) :
    ExpressionFormHasRawType changedSource context (.call callee arguments (.declaration instantiation)) result (.directCall predicates) :=
  CallableLambdaViewStaticTyping.form localView fresh unique (.directCall calleeTyped application argumentTypes) reached

theorem indexed_assignment {canonical changedSource : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (localView : LocalView canonical changedSource changed) (fresh : Avoids canonical roots changed)
    (unique : NodeOccurrencesUnique canonical) {context : SourceSemantics.Context}
    {root : Resolved.LocalId} {key value : ExpressionId} {keyType valueType : TypeSystem.Ty}
    (rootTyped : WritableLocal context root (.mapping keyType valueType))
    (keyTyped : ExpressionHasType canonical context key keyType)
    (valueTyped : ExpressionHasType canonical context value valueType)
    (reached : CallableLambdaViewStaticTyping.Within canonical roots [.expression key, .expression value]) :
    SourceAssignmentHasType changedSource context ⟨⟨root, [.index key], valueType⟩, []⟩ .equal value := by
  apply CallableLambdaViewStaticTyping.assignment localView fresh unique
    (.equal (.intro rootTyped (.index keyTyped (.nil _)) rfl) valueTyped rfl)
  exact reached

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function identity(value: Word) returns (Word) { return value; }",
    "function mixed() returns (Word) { let fn: function() returns (Word) = lam() -> Word { let nested: function() returns (Word) = lam() -> Word { return identity(7); }; let table: mapping(Bool => Word); let count = 0; while (count < 2) { count += 1; if (count == 1) { continue; } table[false] = count; } for (let i = 0; i < 2; i += 1) { match (i) { case 0 { table[true] = nested(); } default { table[true] += 1; } } } return table[true] + table[false]; }; return fn(); }",
    "function failed() returns (Word) { let fn: function() returns (Word) = lam() -> Word { let seen: mapping(Bool => Word); seen[false]; let missing: Word; return missing; }; return fn(); }"
  ]}] }

/- This executable audit uses actual checked lambda inventory. It visits the
reference closure and compares full nodes, including raw metadata. It makes no
claim that metadata equality supplies a canonical compiler success equation. -/
private def auditView (original : TypedSource) (parent : ExpressionNode) : IO Unit := do
  let roots ← match parent.form with
    | .lambda _ _ statements => pure (statements.map NodeId.statement)
    | _ => throw (IO.userError "static view expected lambda inventory")
  let modified := SourceCoreEvidence.withNode original {parent with type := .bool}
  SourceCompilerFeatureSupport.require (original != modified) "static view did not change its enclosing header"
  let mut pending := roots
  let mut seen : List NodeId := []
  while !pending.isEmpty do
    match pending with
    | [] => pure ()
    | next :: rest =>
      pending := rest
      if !(seen.contains next) then
        SourceCompilerFeatureSupport.require (next != .expression parent.id) "static view reached edited parent"
        let node ← match original.lookupNode? next.occurrenceId with
          | some node => pure node
          | none => throw (IO.userError "static view missing reached occurrence")
        SourceCompilerFeatureSupport.require (modified.lookupNode? next.occurrenceId == some node)
          "static view changed reached raw type/evidence/coercion or statement metadata"
        seen := next :: seen
        pending := node.references ++ pending
  SourceCompilerFeatureSupport.require (!seen.isEmpty) "static view empty test body"
  SourceCompilerFeatureSupport.require (SourceCoreDataPlaces.declaredBinders original == SourceCoreDataPlaces.declaredBinders modified)
    "static view changed source binder metadata"

private def failureResume (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let complete ← entry.invoke []
  let token ← match complete.outcome with
    | .failed token _ => pure token
    | _ => throw (IO.userError "static typing fault fixture unexpectedly completed")
  SourceCompilerFeatureSupport.require (← complete.diagnostic token).isSome "static typing fault lost diagnostic"
  for fuel in [0, 10, 100] do
    let started ← SourceCompilerFeatureSupport.get "static typing suspension"
      (← complete.initial.run complete.key [] {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed, complete.outcome with
    | .failed actual heap, .failed expected final =>
      SourceCompilerFeatureSupport.require (actual == expected && heap.heapSize == final.heapSize)
        "static typing resume changed failure effects"
    | _, _ => throw (IO.userError "static typing resume changed outcome")

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "static typing checker" (checkProgram workspace)
  let mut inspected := 0
  for name in ["mixed", "failed"] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    for template in entry.cached.indexed.ancestry.templates.lambdas do
      auditView template.context.inventory.source template.node
      inspected := inspected + 1
    if name == "mixed" then
      let expected := SourceCompilerFeatureSupport.scalar 10
      SourceCompilerFeatureSupport.require ((← entry.run []) == expected) "static typing nested call/loop/match result changed"
      for fuel in [0, 10, 100] do entry.checkResume [] expected fuel
    else failureResume entry
  SourceCompilerFeatureSupport.require (inspected == 3) "static typing did not audit every checked lambda"
  IO.println "lambda full source typing: all 13 judgments, nested/direct/indirect calls, loops/match/keys, exact metadata and resumed effects GREEN"

end Tests.SourceCoreCallableLambdaViewStaticTyping

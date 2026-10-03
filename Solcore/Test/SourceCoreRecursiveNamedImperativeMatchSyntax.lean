import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeMatchSyntaxFactory
import Solcore.Test.SourceCoreUnifiedCorpusSupport
import Solcore.Test.SourceCoreReachableImperativeMatchStatements

/-! The factory replaces an external statement Syntax premise with independent
source typing and finite static leaf/allocator/stopping receipts. No-default-only
stopping remains typed and pointwise. The retained nonsemicolon block fixture
has actual bodyAction acceptance and exact emitted-code equality; public parser
and checked-source provenance for that retained IR view are not claimed. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedImperativeMatchSyntax
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedStatementSyntaxFacts RecursiveNamedImperativeMatchSyntaxFactory

section Formal
variable {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {control : ControlContext} {context final : SourceSemantics.Context} {ids : List StatementId}
  {facts : BodyFacts} {typed : StatementsHaveType source control context ids final facts} {ready : Bool}

theorem actual_typed_syntax (unique : NodeOccurrencesUnique source)
    (receipt : BodyReceipts source expressionSyntax typed ready) (annotation : facts.type = control.returnType) :
    GenericImperativeMatch.Syntax source expressionSyntax context (.statements true ids) control.returnType :=
  syntax_of_typed unique receipt annotation

theorem same_typed_stopping (unique : NodeOccurrencesUnique source)
    (receipt : BodyReceipts source expressionSyntax typed ready) (available : ready = true) :
    ReachableStatementContinuations.StoppingStatements source ids facts.control :=
  receipt.stopping unique available

include typed in
theorem returned_annotation (returned : facts.sawReturn = true) : facts.type = control.returnType :=
  returned_type typed returned
end Formal

section ScopedBlock
variable {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {control : ControlContext} {context innerFinal final : SourceSemantics.Context}
  {id next : StatementId} {node : StatementNode} {body rest : List StatementId}
  {innerFacts tailFacts : BodyFacts}
  (contains : ContainsStatement source id node) (form : node.form = .block body)
  (innerTyped : StatementsHaveType source control context body innerFinal innerFacts)
  (annotation : node.type = innerFacts.type)
  (tailTyped : StatementsHaveType source control context (next :: rest) final tailFacts)
  {innerReady tailReady : Bool}
  (inner : BodyReceipts source expressionSyntax innerTyped innerReady)
  (tail : BodyReceipts source expressionSyntax tailTyped tailReady)
  (tailAnnotation : tailFacts.type = control.returnType)
  (wholeAnnotation : (BodyFacts.cons
    { type := innerFacts.type, hasValue := innerFacts.sawReturn, sawReturn := innerFacts.sawReturn,
      control := innerFacts.control.eraseValue } tailFacts).type = control.returnType)
include contains form innerTyped annotation tailTyped inner tail tailAnnotation wholeAnnotation

/-- A nonreturn value annotation on the inner block needs no Unit restriction. -/
theorem ordinary_scoped_block (unique : NodeOccurrencesUnique source) :
    GenericImperativeMatch.Syntax source expressionSyntax context (.statements true (id :: next :: rest)) control.returnType := by
  have head : StatementReceipts source expressionSyntax
      (StatementHasType.block contains form innerTyped annotation) innerReady := .block (contains := contains) (form := form) (annotation := annotation) inner
  have receipt : BodyReceipts source expressionSyntax
      (StatementsHaveType.cons (StatementHasType.block contains form innerTyped annotation) tailTyped)
      (innerReady || tailReady) := .cons (head := StatementHasType.block contains form innerTyped annotation) (tail := tailTyped) head tail (fun _ => .inl tailAnnotation)
  exact syntax_of_typed unique receipt wholeAnnotation
end ScopedBlock

section PartialIf
variable {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {control : ControlContext} {context thenFinal final : SourceSemantics.Context}
  {id next : StatementId} {node : StatementNode} {condition : ExpressionId} {body rest : List StatementId}
  {bodyFacts tailFacts : BodyFacts}
  (contains : ContainsStatement source id node) (form : node.form = .ifThen condition body none)
  (conditionTyped : ExpressionHasType source context condition .bool)
  (bodyTyped : StatementsHaveType source control context body thenFinal bodyFacts)
  (annotation : node.type = .unit)
  (tailTyped : StatementsHaveType source control context (next :: rest) final tailFacts)
  {bodyReady tailReady : Bool}
  (conditionSyntax : expressionSyntax condition)
  (bodyReceipt : BodyReceipts source expressionSyntax bodyTyped bodyReady)
  (tailReceipt : BodyReceipts source expressionSyntax tailTyped tailReady)
  (tailAnnotation : tailFacts.type = control.returnType)
include contains form conditionTyped bodyTyped annotation tailTyped conditionSyntax bodyReceipt tailReceipt tailAnnotation

/-- A partially returning ordinary if keeps Unit and the actual typed tail. -/
theorem partial_if_with_tail (unique : NodeOccurrencesUnique source) :
    GenericImperativeMatch.Syntax source expressionSyntax context (.statements true (id :: next :: rest)) control.returnType := by
  have head : StatementReceipts source expressionSyntax
      (StatementHasType.ifWithoutElse contains form conditionTyped bodyTyped annotation) false :=
    .ifWithoutElse (contains := contains) (form := form) (conditionTyped := conditionTyped) (annotation := annotation) conditionSyntax bodyReceipt
  have receipt : BodyReceipts source expressionSyntax
      (StatementsHaveType.cons (StatementHasType.ifWithoutElse contains form conditionTyped bodyTyped annotation) tailTyped)
      (false || tailReady) := .cons (head := StatementHasType.ifWithoutElse contains form conditionTyped bodyTyped annotation) (tail := tailTyped) head tailReceipt (fun _ => .inl tailAnnotation)
  exact syntax_of_typed unique receipt (by simp [BodyFacts.cons, tailAnnotation])
end PartialIf

section ReachedTail
variable {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {control : ControlContext} {context : SourceSemantics.Context} {id next : StatementId}
  {node : StatementNode} {resolution : MatchResolution} {type : TypeSystem.Ty}
  {caseFacts : List BodyFacts} {summary : ControlSummary}
  (contains : ContainsStatement source id node) (form : node.form = .matchWith resolution)
  (absent : resolution.defaultBody = none)
  (scrutineeTyped : ExpressionHasType source context resolution.scrutinee type)
  (casesTyped : MatchCasesHaveType source control context type resolution.cases caseFacts)
  (requirements : resolution.requirements = resolution.cases.flatMap (fun arm => arm.pattern.requirements))
  (exhaustive : MatchExhaustive context type resolution.cases none)
  (merged : mergeBodyControls caseFacts none = some summary)
  (annotation : node.type = if allBodiesSawReturn caseFacts then control.returnType else .unit)
  {caseReady : Bool} (scrutinee : expressionSyntax resolution.scrutinee)
  (casesReceipt : CasesReceipts source expressionSyntax casesTyped caseReady)
  (hidden : source.inputs.any (fun input => decide (input.id = resolution.hiddenScrutinee)) = false)
  (ordinary : ∀ arm ∈ resolution.cases, ∀ binder ∈ arm.pattern.binderIds,
    source.inputs.any (fun input => decide (input.id = binder)) = false)
  {final : SourceSemantics.Context} {rest : List StatementId} {tailFacts : BodyFacts}
  (tailTyped : StatementsHaveType source control context (next :: rest) final tailFacts)
  {tailReady : Bool} (tail : BodyReceipts source expressionSyntax tailTyped tailReady)
  (tailReturns : tailFacts.sawReturn = true) (tailAnnotation : tailFacts.type = control.returnType)
include contains form absent scrutineeTyped casesTyped requirements exhaustive merged annotation
  scrutinee casesReceipt hidden ordinary tailTyped tail tailReturns tailAnnotation

/-- No-default heads are admitted when the actual typed continuation returns.
They are not globally excluded or promoted to universal stopping. -/
theorem no_default_with_typed_tail (unique : NodeOccurrencesUnique source) :
    GenericImperativeMatch.Syntax source expressionSyntax context (.statements true (id :: next :: rest)) control.returnType := by
  let headTyped := StatementHasType.matchWithoutDefault contains form absent scrutineeTyped casesTyped requirements exhaustive merged annotation
  have head : StatementReceipts source expressionSyntax headTyped false :=
    .matchWithoutDefault (contains := contains) (form := form) (absent := absent)
      (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (requirements := requirements)
      (exhaustive := exhaustive) (merged := merged) (annotation := annotation) scrutinee casesReceipt hidden ordinary
  have receipt : BodyReceipts source expressionSyntax (StatementsHaveType.cons headTyped tailTyped) (false || tailReady) :=
    .cons (head := headTyped) (tail := tailTyped) head tail (fun _ => .inl tailAnnotation)
  exact syntax_of_typed unique receipt (by simp [BodyFacts.cons, tailReturns, tailAnnotation])
end ReachedTail

section Boundaries
variable {source : TypedSource} {context : SourceSemantics.Context} {expressionSyntax : ExpressionId → Prop}
  {control : ControlContext} {mode : Bool} {expected : TypeSystem.Ty}

/-- An empty typed body authenticates no universal stopping selection. -/
theorem empty_has_no_stopping :
    ¬ ReachableStatementContinuations.StoppingStatements source [] (BodyFacts.empty.control) := by
  intro stopped
  exact stopped.nonempty rfl

/-- The new scoped block does not change reachable nil's result restriction. -/
theorem nil_nonunit (nonunit : expected ≠ .unit) :
    ¬ GenericImperativeMatch.Syntax source expressionSyntax context (.statements true []) expected := by
  intro tree
  cases tree with
  | body lexical => cases lexical with
    | nil allowed => rcases allowed with impossible | unit; cases impossible; exact nonunit unit

abbrev no_default_universal := @Tests.SourceCoreReachableImperativeMatchStatements.no_default_match_has_no_stopping_head

/-- The actual ordinary-if form, independent typing and source uniqueness
identify its retained Unit annotation. -/
theorem partial_if_annotation {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {body : List StatementId} {final : SourceSemantics.Context} {facts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (typed : StatementHasType source control context id final facts)
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition body none) :
    node.type = .unit := by
  have sameNode : ∀ actual, ContainsStatement source id actual → actual = node := by
    intro actual contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases typed <;> have same := sameNode _ (by assumption) <;> cases same <;> simp_all
end Boundaries

/-- The actual compiler entry consumes the new syntax factory, with completion,
residual context and all original callback equations retained. -/
abbrev actual_body_extraction := @RecursiveNamedImperativeMatchSyntaxFactory.extraction_of_typed_body

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def content : String := String.intercalate "\n" [
 "function partialIf(seed: Word) returns (Word) { if (seed == 0) { return 17; } return 23; }",
 "function partialBoth(seed: Word) returns (Word) { if (seed == 0) { if (seed == 1) { return 29; } } else { if (seed == 2) { return 31; } } return 37; }",
 "function totalIf(seed: Word) returns (Word) { if (seed == 0) { return 41; } else { return 43; } }",
 "function blockFalls(seed: Word) returns (Word) { { if (seed == 0) { return 47; } } return 53; }",
 "function scopedValue() returns (Word) { { 61; } return 67; }",
 "function faultBefore(seed: Word) returns (Word) { if (seed == 0) { let gap: Word; return gap; } return 97; }"
]
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  let result ← get "Syntax factory checkpoint resume" (SourceCoreUnifiedCompilation.Result.resume first 300000)
  pure result.observation

def run : IO Unit := do
 let compiled ← SourceCoreUnifiedCorpusSupport.prepare "Syntax factory annotation audit" content
   ["partialIf", "partialBoth", "totalIf", "blockFalls", "scopedValue", "faultBefore"]
 let prepared := compiled.indexed
 let diagnostic ← match prepared.base.diagnostics with
   | none => throw (IO.userError "annotation diagnostics missing") | some diagnostic => pure diagnostic.program
 let diagnostic := match prepared.base.callableContext with
   | none => diagnostic | some native => {diagnostic with rootTable := native.diagnostics.rootTable}
 let parents ← get "annotation contexts" (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
   (prepared.base.locals.bindings.flatMap (·.instances)))
 for named in prepared.base.functions do
  let source := CallableIndexedNamedGeneration.source named
  let own ← match diagnostic.base.find? named.signature.key with
    | none => throw (IO.userError "annotation own diagnostics missing") | some own => pure own
  let statements ← get "annotation roots" (source.roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
    | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
  let body ← get "annotation actual body" (CallableIndexedNamedGeneration.bodyAction prepared named diagnostic parents own statements)
  IO.println s!"actual accepted body key={reprStr named.signature.key} result={reprStr named.signature.resultType}"
  let mut ifTypes : List TypeSystem.Ty := []
  for item in source.nodes do
   match item with
   | .statement node => match node.form with
     | .ifThen _ _ otherwise =>
       ifTypes := ifTypes ++ [node.type]
       IO.println s!"  if annotation={reprStr node.type} else={otherwise.isSome}"
     | .block _ => IO.println s!"  block annotation={reprStr node.type}"
     | _ => pure ()
   | _ => pure ()
  if some named.signature.key == compiled.keys[0]? then
    require (ifTypes == [.unit]) "partial if annotation is non-Unit"
  if some named.signature.key == compiled.keys[1]? then
    require (ifTypes.length == 3 && ifTypes.all (· == .unit)) "partial both annotation is non-Unit"
  if some named.signature.key == compiled.keys[2]? then
    require (ifTypes == [.word]) "total if annotation is not actual return type"
  if some named.signature.key == compiled.keys[4]? then
   let block ← match statements with
     | id :: _ => pure id | [] => throw (IO.userError "retained block root missing")
   let blockNode ← match source.lookupStatement? block with
     | some node => pure node | none => throw (IO.userError "retained block lookup missing")
   let inner ← match blockNode.form with
     | .block [inner] => pure inner | _ => throw (IO.userError "retained singleton block missing")
   let raw : TypedSource := {source with nodes := source.nodes.map fun
     | .statement node =>
       if node.id == block then .statement {node with type := .word}
       else if node.id == inner then match node.form with
         | .expression expression true => .statement {node with type := .word, form := .expression expression false}
         | _ => .statement node
       else .statement node
     | other => other}
   let retained : SourceCoreGeneralFunctions.Function := {named with specialized := {named.specialized with
     function := {named.specialized.function with typedBody := raw}}}
   let retainedBody ← get "retained ordinary non-Unit block actual bodyAction"
     (CallableIndexedNamedGeneration.bodyAction prepared retained diagnostic parents own statements)
   require (retainedBody == body) "retained ordinary non-Unit block changed actual code"
   IO.println "retained IR ordinary block: Word annotation + non-semicolon Word child, actual bodyAction accepted with identical emitted code"
 let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (.word (Word.ofNatModulo 811))⟩]}
 let scenarios := [("partialIf", 0, 17), ("partialIf", 1, 23),
     ("partialBoth", 0, 37), ("partialBoth", 2, 31), ("partialBoth", 3, 37),
     ("totalIf", 0, 41), ("totalIf", 1, 43), ("blockFalls", 0, 47), ("blockFalls", 1, 53),
     ("faultBefore", 1, 97)]
 for (name, seed, expected) in scenarios do
   let arguments := [SourceTypedRuntime.Value.word (Word.ofNatModulo seed)]
   let baseline ← finish compiled name arguments 300000 initial
   for fuel in [0, 1, 31, 300000] do
     let observed ← finish compiled name arguments fuel initial
     require (reprStr observed == reprStr baseline) s!"Syntax factory resume changed {name}"
     match observed with
     | .done value final =>
       require (reprStr value == reprStr (SourceTypedRuntime.Value.word (Word.ofNatModulo expected)))
         s!"Syntax factory result changed {name}"
       require (reprStr final.heap == reprStr (initial.heap ++ [⟨.word, some (.word (Word.ofNatModulo seed))⟩]))
         s!"Syntax factory complete ordered heap changed {name}"
     | other => throw (IO.userError s!"Syntax factory expected success {name}: {reprStr other}")
 for fuel in [0, 1, 31, 300000] do
   let observed ← finish compiled "faultBefore" [.word (Word.ofNatModulo 0)] fuel initial
   match observed with
   | .fault (.uninitializedLocal _) final =>
     require (reprStr final.heap == reprStr (initial.heap ++ [⟨.word, some (.word (Word.ofNatModulo 0))⟩, ⟨.word, none⟩]))
       "Syntax factory fault changed full heap or executed continuation"
   | other => throw (IO.userError s!"Syntax factory expected original fault: {reprStr other}")
 let baseline ← finish compiled "scopedValue" [] 300000 initial
 for fuel in [0, 1, 31, 300000] do
   let observed ← finish compiled "scopedValue" [] fuel initial
   require (reprStr observed == reprStr baseline) "ordinary scoped value resume changed"
   match observed with
   | .done value final =>
     require (reprStr value == reprStr (SourceTypedRuntime.Value.word (Word.ofNatModulo 67))) "ordinary scoped value result changed"
     require (reprStr final.heap == reprStr initial.heap) "ordinary scoped value changed full heap"
   | other => throw (IO.userError s!"ordinary scoped value expected success: {reprStr other}")
 IO.println "Syntax factory GREEN: six actual roots, ordinary/terminal annotation boundary, retained IR bodyAction/code Eq, full heap/fault/resume"

end Tests.SourceCoreRecursiveNamedImperativeMatchSyntax

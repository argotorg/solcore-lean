import Solcore.SourceSemantics.CoreLowering.ImperativeNativePolicyTyping
import Solcore.Test.SourceCompilerFeatureSupport

/-! A concrete typed callback profile exercises the actual statement/header
compiler without assuming the whole body's native type. The profile covers
Word/Bool constants and ordinary Word cells. It claims native typing only.
Public fixtures separately retain real callback execution and resumption. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreImperativeNativePolicyTyping
open Solcore Core Frontend SourceInference SourceSemantics.CoreLowering
open ImperativeNativePolicyTyping

private def expressions : SourceCoreLoops.ExpressionLowerer := fun _ source _ id _ =>
  match source.lookupExpression? id with
  | none => .error (.traversalExhausted (.occurrence id.occurrence))
  | some node => match node.type with
    | .word => .ok ⟨.word, LanguageResult.success (.word (Word.ofNatModulo 7))⟩
    | .bool => .ok ⟨.bool, LanguageResult.success (.bool false)⟩
    | _ => .error (.traversalExhausted (.occurrence id.occurrence))

private def policy : SourceCoreLoops.Policy := {
  lowerExpression := expressions
  lowerBinder := fun _ _ _ => .ok .word
  lowerAssignment := fun source _ _ _ => .error (.traversalExhausted (.declaration source.owner)) }

/-- Native laws for real callbacks, including both actual default allocation
wrappers. Unsupported assignment/match callbacks cannot manufacture code. -/
theorem callback_laws (definitions : DataEnvironment) (administrative : Core.Context) :
    PolicyLaws definitions administrative (fun _ _ => True) policy := by
  constructor
  · intro fuel source scope id reasonAt lowered _ accepted
    change expressions fuel source scope id reasonAt = .ok lowered at accepted
    unfold expressions at accepted
    cases found : source.lookupExpression? id with
    | none => simp [found] at accepted
    | some node =>
      simp only [found] at accepted
      cases typeEq : node.type <;> simp only [typeEq] at accepted <;> try cases accepted
      rename_i constructor
      cases constructor with
      | declaration id => cases accepted
      | builtin builtin =>
        cases builtin <;> cases accepted
        all_goals exact LanguageResult.success_hasType (by constructor)
  · intro source scope binder type _ accepted
    cases accepted
    exact ⟨.word, True.intro⟩
  · intro source scope binder payload output body code _ payloadWF _ bodyTyped accepted
    change Except.ok (LocalSequence.letUninitialized payload body) = Except.ok code at accepted
    cases accepted
    exact LocalSequence.letUninitialized_hasType payloadWF
      (by simpa [context, SourceCoreLocalCell.coreContext, OptionalCell.referenceType] using bodyTyped)
  · intro source scope binder payload output initializer body code _ _ outputWF initialTyped bodyTyped accepted
    change Except.ok (LocalSequence.letInitialized output payload initializer body) = Except.ok code at accepted
    cases accepted
    exact LocalSequence.letInitialized_hasType outputWF initialTyped
      (by simpa [context, SourceCoreLocalCell.coreContext, OptionalCell.referenceType] using bodyTyped)
  · intro fuel source scope site assignment operator rhs output body reasonAt code _ _ _ accepted
    cases operator <;> simp [SourceCoreLoops.assignValue, policy, bind, Except.bind] at accepted
  · intro callback source scope site assignment output body code selected
    cases selected
  · intro callback fuel source scope site assignment output body reasonAt code selected
    cases selected
  · intro callback flow fuel source scope id resolution type reasonAt selfReason code selected
    cases selected

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"imperative_native", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "imperative_native.solc"⟩, 0, 1⟩
private def expression (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index + 2⟩⟩
private def binder (index : Nat) : TypedBinder := ⟨⟨owner, index⟩, "value", .mono .word, [], false, none⟩
private def wordNode : ExpressionNode := { id := expression 0, span, type := .word, form := .literal (.decimal "7") }
private def boolNode : ExpressionNode := { id := expression 1, span, type := .bool, form := .reference "false" (.builtinBoolean false) }
private def absent : StatementNode := ⟨statement 0, span, .unit, .letDecl (binder 0) none⟩
private def present : StatementNode := ⟨statement 1, span, .unit, .letDecl (binder 1) (some (expression 0))⟩
private def conditional : StatementNode := ⟨statement 2, span, .unit, .ifThen (expression 1) [statement 6] (some [])⟩
private def whileNode : StatementNode := ⟨statement 3, span, .unit, .whileLoop (expression 1) [statement 7]⟩
private def forNode : StatementNode := ⟨statement 4, span, .unit,
  .forLoop [.letDecl (binder 2) (some (expression 0))] (expression 1) [.expression (expression 0)] [statement 7]⟩
private def returned : StatementNode := ⟨statement 5, span, .word, .returnStmt (some (expression 0))⟩
private def breaking : StatementNode := ⟨statement 6, span, .unit, .breakStmt⟩
private def continuing : StatementNode := ⟨statement 7, span, .unit, .continueStmt⟩
private def statements : List StatementId := [statement 0, statement 1, statement 2, statement 3, statement 4, statement 5]
private def source : TypedSource := {
  owner, inputs := [], roots := statements.map (.statement ·)
  nodes := [.expression wordNode, .expression boolNode, .statement absent, .statement present,
    .statement conditional, .statement whileNode, .statement forNode, .statement returned,
    .statement breaking, .statement continuing] }
private def reasonAt : ExpressionId → Word := fun _ => Word.ofNatModulo 29
private def action := SourceCoreLoops.lowerStatementsWithPolicy policy 32 source [] statements .word reasonAt
  (Word.ofNatModulo 31) (Word.ofNatModulo 37)

/-- All allocated scopes, loop children and finish are derived from the actual
accepted compiler action under arbitrary hidden administrative types. -/
theorem accepted_fixture {code : Expr} (administrative : Core.Context)
    (accepted : action = .ok code) :
    HasType administrative code (LanguageResult.resultType .word) [] := by
  simpa [context, SourceCoreLocalCell.coreContext] using
    (body_native (callback_laws [] administrative) True.intro Ty.WellFormed.word accepted)

/-- The interface rejects a callback that reports Word while emitting Unit.
Successful result annotations alone do not establish a native type. -/
theorem wrong_callback_rejected :
    ¬ PolicyLaws [] [] (fun _ _ => True)
      {policy with lowerExpression := fun _ _ _ _ _ => .ok ⟨.word, .unit⟩} := by
  intro laws
  have typed := laws.expression 0 source [] (expression 0) reasonAt ⟨.word, .unit⟩ True.intro rfl
  cases typed

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function make(seed: Word) returns (function() returns (Word)) { return lam() -> Word { let value: Word = seed; for (let i: Word = 0; i < 3; i += 1) { value += 1; } while (value < 6) { value += 1; } return value; }; }"}] }

def run : IO Unit := do
  let code ← SourceCompilerFeatureSupport.get "imperative native compiler fixture" action
  let expected := LanguageResult.resultType .word
  for hidden in [[], [.integer, .function .unit .word]] do
    SourceCompilerFeatureSupport.require (Core.infer? hidden code [] == some expected)
      "imperative traversal lost its native type under hidden slots"
  let initial := State.initial code
  let final ← match Core.runStateful 100000 initial with
    | .done value store => pure (value, store)
    | _ => throw (IO.userError "typed imperative fixture did not complete")
  SourceCompilerFeatureSupport.require (final.1 == .inRight .word (.word (Word.ofNatModulo 7)))
    "imperative native fixture returned the wrong result"
  for spent in [0, 13, 67] do
    let resumed := match Core.runStateful spent initial with
      | .outOfFuel checkpoint => Core.runStateful 100000 checkpoint
      | done => done
    match resumed with
    | .done value store =>
      SourceCompilerFeatureSupport.require (value == final.1 && reprStr store == reprStr final.2)
        "imperative native resumption changed its exact result or store"
    | _ => throw (IO.userError "imperative native resumption did not complete")
  let checked ← SourceCompilerFeatureSupport.get "imperative lambda checker" (checkProgram workspace)
  let entry ← SourceCompilerFeatureSupport.compileNamed checked "make"
  let created ← entry.invoke [.word (Word.ofNatModulo 2)]
  let completed ← match created.outcome with
    | .succeeded completion => pure completion
    | _ => throw (IO.userError "imperative lambda creation failed")
  let handle ← match completed.value with
    | .function handle => pure handle
    | _ => throw (IO.userError "imperative lambda handle absent")
  let invoked ← SourceCompilerFeatureSupport.get "imperative lambda invocation"
    (← completed.session.invokePacked handle .unit SourceCompilerFeatureSupport.executionOptions)
  match invoked with
  | .succeeded completion =>
    SourceCompilerFeatureSupport.require (completion.value == .word (Word.ofNatModulo 6))
      "real imperative lambda capture/body changed"
  | _ => throw (IO.userError "real imperative lambda body failed")
  IO.println "imperative native policy: actual traversal, typed callbacks, hidden slots, exact store/resume and captured lambda GREEN"

end Tests.SourceCoreImperativeNativePolicyTyping

import Solcore.Frontend.RustHull.LoopLoweringStructure
import Solcore.Frontend.RustHull.DerivationCorrespondenceSupport
import Solcore.Core.LocalLoopCorrespondence

/-! A source loop derivation reuses the one self closure installed by the actual
compiler. Condition, body and post computations may allocate further closures;
each stage therefore retains its actual environment and store. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LoopDerivationCorrespondence
open Correspondence DerivationCorrespondence StatementCorrespondence

/-- Simulation of an already installed loop closure, at a fixed source
configuration. Iteration does not allocate another self cell. -/
def LoopSimulation {σ : Type} (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (test : Expr) (post body : List Stmt)
    (initial : Semantics.State σ) (control : Semantics.Control) (final : Semantics.State σ) : Prop :=
  SafeControl control →
  ∀ {scope result loops} (compiled : LoopLoweringStructure.Compiled signatures scope result loops test post body),
  ∀ {world mapping environment store location},
    EnvironmentRel world sourceEnvironment scope mapping environment →
    GlobalEnvironmentRel codes locations scope mapping environment →
    HeapRel world initial.heap store → InstalledGlobals codes locations captured store →
    store.read? location = some (.inRight .unit
      (Core.LocalLoop.installedClosure result (compiled.conditionCore.rename mapping)
        (compiled.bodyCore.rename mapping) (compiled.postCore.rename mapping)
        (Core.Word.ofNatModulo 3) location environment)) →
    ∃ extension target finalStore,
      ControlRel result control target ∧
      Core.Evaluates (Core.LocalLoop.conditionPrefix result location ++ environment) store
        (Core.LocalLoop.loopBody result (compiled.conditionCore.rename mapping)
          (compiled.bodyCore.rename mapping) (compiled.postCore.rename mapping) (Core.Word.ofNatModulo 3))
        target finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧
      InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore

def LoopMotive {σ : Type} (functions : List Function) (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (test : Expr) (post body : List Stmt)
    (initial : Semantics.State σ) (control : Semantics.Control) (final : Semantics.State σ) : Prop :=
  RecursiveExpression functions test →
  (∀ statement ∈ post, RecursiveStatement functions statement) →
  (∀ statement ∈ body, RecursiveStatement functions statement) →
  LoopSimulation signatures codes locations captured sourceEnvironment test post body initial control final

variable {σ : Type} {signatures : List Signature} {codes : List GlobalCode}
  {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}

/-- Instantiate the condition IH under the exact administrative prefix of a
loop stage, including any heap effects performed while testing it. -/
theorem test_at {test : Expr} {initial final : Semantics.State σ} {value : Semantics.Value}
    {truth : Bool}
    (evaluated : ExprSimulation signatures codes locations captured sourceEnvironment test initial (.value value) final)
    (tested : Semantics.condition? value = some truth)
    {fuel : Nat} {scope : Scope} {lowered : Lowered} {expression : Core.Expr}
    (compiled : lowerExpression fuel signatures scope test = .ok lowered)
    (converted : condition lowered = .ok expression)
    (extra : Core.Environment)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (locals : EnvironmentRel world sourceEnvironment scope mapping environment)
    (globals : GlobalEnvironmentRel codes locations scope mapping environment)
    (heap : HeapRel world initial.heap store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension finalStore,
      Core.Evaluates (extra ++ environment) store
        ((expression.rename mapping).rename (Core.LocalLoop.shift extra.length))
        (.inRight .word (.bool truth)) finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧
      InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore := by
  obtain ⟨extension, target, finalStore, related, execution, finalHeap, finalInstalled, frame⟩ :=
    evaluated rfl compiled (locals.prepend extra) (globals.prepend extra) heap installed
  have conditionExecution := ExpressionCorrespondence.condition_evaluates converted related tested execution
  exact ⟨extension, finalStore,
    by rw [Core.Expr.rename_comp]; exact conditionExecution,
    finalHeap, finalInstalled, frame⟩

/-- Instantiate a body or post IH at its actual control-transfer prefix. -/
theorem statements_at {statements : List Stmt} {initial final : Semantics.State σ}
    {control : Semantics.Control}
    (evaluated : StatementsSimulation signatures codes locations captured sourceEnvironment statements initial control final)
    (safe : SafeControl control)
    {fuel : Nat} {scope : Scope} {result : Core.Ty} {loops : Nat} {expression : Core.Expr}
    (compiled : lowerStatements fuel signatures scope result loops statements = .ok expression)
    (extra : Core.Environment)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (locals : EnvironmentRel world sourceEnvironment scope mapping environment)
    (globals : GlobalEnvironmentRel codes locations scope mapping environment)
    (heap : HeapRel world initial.heap store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension target finalStore,
      ControlRel result control target ∧
      Core.Evaluates (extra ++ environment) store
        ((expression.rename mapping).rename (Core.LocalLoop.shift extra.length)) target finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧
      InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore := by
  obtain ⟨extension, target, finalStore, related, execution, finalHeap, finalInstalled, frame⟩ :=
    evaluated safe compiled (locals.prepend extra) (globals.prepend extra) heap installed
  exact ⟨extension, target, finalStore, related,
    by rw [Core.Expr.rename_comp]; exact execution,
    finalHeap, finalInstalled, frame⟩


/-- The public loop statement allocates and installs its actual self closure
once, then enters the loop derivation. -/
theorem statement {statement : Stmt} {test : Expr} {post body : List Stmt}
    {initial final : Semantics.State σ} {control : Semantics.Control}
    (kind : statement.kind = .forLoop [] test post body)
    (continued : LoopSimulation signatures codes locations captured sourceEnvironment test post body initial control final) :
    StmtSimulation signatures codes locations captured sourceEnvironment statement initial control final := by
  intro safe fuel scope result loops expression compiled world mapping environment store
    locals globals heap installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      obtain ⟨conditionCode, conditionCore, bodyCore, postCore,
        conditionCompiled, conditionConverted, bodyCompiled, postCompiled, rfl⟩ :=
        LoopLoweringStructure.empty_init_components compiled
      let code : LoopLoweringStructure.Compiled signatures scope result loops test post body :=
        ⟨fuel, conditionCode, conditionCore, bodyCore, postCore,
          conditionCompiled, conditionConverted, bodyCompiled, postCompiled⟩
      let cell := Core.Value.inRight .unit (Core.LocalLoop.installedClosure result
        (conditionCore.rename mapping) (bodyCore.rename mapping) (postCore.rename mapping)
        (Core.Word.ofNatModulo 3) store.length environment)
      have self : (store ++ [cell]).read? store.length = some cell := by simp [Core.Store.read?]
      obtain ⟨extension, target, finalStore, related, executed, finalHeap, finalInstalled, frame⟩ :=
        continued safe code locals globals (heap.appendCore [cell]) (installed.append [cell]) self
      refine ⟨extension, target, finalStore, related, ?_, finalHeap, finalInstalled,
        ClosuresPreserved.trans (ClosuresPreserved.append store [cell]) frame⟩
      rw [Core.LocalLoop.iterate_rename]
      exact Core.LocalLoop.iterate_start result (Core.Word.ofNatModulo 3) executed

/-- Initializers retain the exact compiler's statement-list scope and control
behavior before reaching the single allocation above. -/
theorem initialized_statement {statement : Stmt} {test : Expr} {init post body : List Stmt}
    {initial final : Semantics.State σ} {control : Semantics.Control}
    (kind : statement.kind = .forLoop init test post body) (nonempty : init ≠ [])
    (continued : StatementsSimulation signatures codes locations captured sourceEnvironment
      (init ++ [⟨.forLoop [] test post body, statement.span⟩]) initial control final) :
    StmtSimulation signatures codes locations captured sourceEnvironment statement initial control final := by
  intro safe fuel scope result loops expression compiled
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel => exact continued safe (LoopLoweringStructure.nonempty_init nonempty compiled)

theorem fault (test : Expr) (post body : List Stmt) (initial final : Semantics.State σ)
    (reason : Semantics.Fault) :
    LoopSimulation signatures codes locations captured sourceEnvironment test post body initial (.fault reason) final := by
  intro impossible
  cases impossible

theorem done {test : Expr} {post body : List Stmt} {initial final : Semantics.State σ}
    {value : Semantics.Value}
    (tested : ExprSimulation signatures codes locations captured sourceEnvironment test initial (.value value) final)
    (truth : Semantics.condition? value = some false) :
    LoopSimulation signatures codes locations captured sourceEnvironment test post body initial .fallthrough final := by
  intro _ scope result loops compiled world mapping environment store location locals globals heap installed _
  obtain ⟨extension, finalStore, executed, finalHeap, finalInstalled, frame⟩ :=
    test_at tested truth compiled.conditionCompiled compiled.conditionConverted
      (Core.LocalLoop.conditionPrefix result location) locals globals heap installed
  exact ⟨extension, _, finalStore, .fallthrough,
    Core.LocalLoop.loopBody_done result (Core.Word.ofNatModulo 3) location executed,
    finalHeap, finalInstalled, frame⟩

theorem body_break {test : Expr} {post body : List Stmt}
    {initial testedState final : Semantics.State σ} {value : Semantics.Value}
    (tested : ExprSimulation signatures codes locations captured sourceEnvironment test initial (.value value) testedState)
    (truth : Semantics.condition? value = some true)
    (executed : StatementsSimulation signatures codes locations captured sourceEnvironment body testedState .breaking final) :
    LoopSimulation signatures codes locations captured sourceEnvironment test post body initial .fallthrough final := by
  intro _ scope result loops compiled world mapping environment store location locals globals heap installed _
  obtain ⟨testExtension, testedStore, testEvaluation, testedHeap, testedInstalled, testFrame⟩ :=
    test_at tested truth compiled.conditionCompiled compiled.conditionConverted
      (Core.LocalLoop.conditionPrefix result location) locals globals heap installed
  obtain ⟨bodyExtension, target, finalStore, related, bodyEvaluation, finalHeap, finalInstalled, bodyFrame⟩ :=
    statements_at executed trivial compiled.bodyCompiled (Core.LocalLoop.bodyPrefix result location)
      (locals.extendWorld testExtension) globals testedHeap testedInstalled
  cases related
  exact ⟨testExtension ++ bodyExtension, _, finalStore, .fallthrough,
    Core.LocalLoop.loopBody_bodyBreak result (Core.Word.ofNatModulo 3) location testEvaluation bodyEvaluation,
    by simpa only [List.append_assoc] using finalHeap,
    finalInstalled, ClosuresPreserved.trans testFrame bodyFrame⟩

theorem body_stop {test : Expr} {post body : List Stmt}
    {initial testedState final : Semantics.State σ} {value : Semantics.Value} {control : Semantics.Control}
    (tested : ExprSimulation signatures codes locations captured sourceEnvironment test initial (.value value) testedState)
    (truth : Semantics.condition? value = some true)
    (executed : StatementsSimulation signatures codes locations captured sourceEnvironment body testedState control final)
    (stopped : (∃ value, control = .returned value) ∨ (∃ reason, control = .fault reason)) :
    LoopSimulation signatures codes locations captured sourceEnvironment test post body initial control final := by
  intro safe scope result loops compiled world mapping environment store location locals globals heap installed _
  rcases stopped with ⟨source, rfl⟩ | ⟨reason, rfl⟩
  · obtain ⟨testExtension, testedStore, testEvaluation, testedHeap, testedInstalled, testFrame⟩ :=
      test_at tested truth compiled.conditionCompiled compiled.conditionConverted
        (Core.LocalLoop.conditionPrefix result location) locals globals heap installed
    obtain ⟨bodyExtension, target, finalStore, related, bodyEvaluation, finalHeap, finalInstalled, bodyFrame⟩ :=
      statements_at executed safe compiled.bodyCompiled (Core.LocalLoop.bodyPrefix result location)
        (locals.extendWorld testExtension) globals testedHeap testedInstalled
    cases related with
    | returned valueRelated =>
        exact ⟨testExtension ++ bodyExtension, _, finalStore, .returned valueRelated,
          Core.LocalLoop.loopBody_bodyReturn result (Core.Word.ofNatModulo 3) location testEvaluation bodyEvaluation,
          by simpa only [List.append_assoc] using finalHeap,
          finalInstalled, ClosuresPreserved.trans testFrame bodyFrame⟩
  · cases safe

private theorem progress_safe {control : Semantics.Control}
    (progress : control = .fallthrough ∨ control = .continuing) : SafeControl control := by
  rcases progress with rfl | rfl <;> trivial

private theorem progress_value {result : Core.Ty} {control : Semantics.Control} {value : Core.Value}
    (related : ControlRel result control value)
    (progress : control = .fallthrough ∨ control = .continuing) :
    ∃ flag, value = Core.LocalLoop.advanceValue result flag := by
  rcases progress with rfl | rfl
  · cases related; exact ⟨false, rfl⟩
  · cases related; exact ⟨true, rfl⟩

theorem step {test : Expr} {post body : List Stmt}
    {initial testedState bodyState postState final : Semantics.State σ}
    {value : Semantics.Value} {bodyControl postControl control : Semantics.Control}
    (tested : ExprSimulation signatures codes locations captured sourceEnvironment test initial (.value value) testedState)
    (truth : Semantics.condition? value = some true)
    (bodyExecuted : StatementsSimulation signatures codes locations captured sourceEnvironment body testedState bodyControl bodyState)
    (bodyContinues : bodyControl = .fallthrough ∨ bodyControl = .continuing)
    (postExecuted : StatementsSimulation signatures codes locations captured sourceEnvironment post bodyState postControl postState)
    (postContinues : postControl = .fallthrough ∨ postControl = .continuing)
    (continued : LoopSimulation signatures codes locations captured sourceEnvironment test post body postState control final) :
    LoopSimulation signatures codes locations captured sourceEnvironment test post body initial control final := by
  intro safe scope result loops compiled world mapping environment store location locals globals heap installed self
  obtain ⟨testExtension, testedStore, testEvaluation, testedHeap, testedInstalled, testFrame⟩ :=
    test_at tested truth compiled.conditionCompiled compiled.conditionConverted
      (Core.LocalLoop.conditionPrefix result location) locals globals heap installed
  obtain ⟨bodyExtension, bodyTarget, bodyStore, bodyRelated, bodyEvaluation, bodyHeap, bodyInstalled, bodyFrame⟩ :=
    statements_at bodyExecuted (progress_safe bodyContinues) compiled.bodyCompiled
      (Core.LocalLoop.bodyPrefix result location)
      (locals.extendWorld testExtension) globals testedHeap testedInstalled
  obtain ⟨bodyFlag, rfl⟩ := progress_value bodyRelated bodyContinues
  obtain ⟨postExtension, postTarget, postStore, postRelated, postEvaluation, postHeap, postInstalled, postFrame⟩ :=
    statements_at postExecuted (progress_safe postContinues) compiled.postCompiled
      (Core.LocalLoop.postPrefix result location bodyFlag)
      ((locals.extendWorld testExtension).extendWorld bodyExtension) globals bodyHeap bodyInstalled
  simp only [Core.LocalLoop.postPrefix_length] at postEvaluation
  obtain ⟨postFlag, rfl⟩ := progress_value postRelated postContinues
  have retained := postFrame (bodyFrame (testFrame self))
  obtain ⟨nextExtension, target, finalStore, related, nextEvaluation, finalHeap, finalInstalled, nextFrame⟩ :=
    continued safe compiled
      (((locals.extendWorld testExtension).extendWorld bodyExtension).extendWorld postExtension)
      globals postHeap postInstalled retained
  exact ⟨testExtension ++ bodyExtension ++ postExtension ++ nextExtension, target, finalStore, related,
    Core.LocalLoop.loopBody_step result (Core.Word.ofNatModulo 3) location bodyFlag postFlag
      testEvaluation bodyEvaluation postEvaluation retained nextEvaluation,
    by simpa only [List.append_assoc] using finalHeap, finalInstalled,
    ClosuresPreserved.trans testFrame (ClosuresPreserved.trans bodyFrame
      (ClosuresPreserved.trans postFrame nextFrame))⟩

theorem post_break {test : Expr} {post body : List Stmt}
    {initial testedState bodyState final : Semantics.State σ}
    {value : Semantics.Value} {bodyControl : Semantics.Control}
    (tested : ExprSimulation signatures codes locations captured sourceEnvironment test initial (.value value) testedState)
    (truth : Semantics.condition? value = some true)
    (bodyExecuted : StatementsSimulation signatures codes locations captured sourceEnvironment body testedState bodyControl bodyState)
    (bodyContinues : bodyControl = .fallthrough ∨ bodyControl = .continuing)
    (postExecuted : StatementsSimulation signatures codes locations captured sourceEnvironment post bodyState .breaking final) :
    LoopSimulation signatures codes locations captured sourceEnvironment test post body initial .fallthrough final := by
  intro _ scope result loops compiled world mapping environment store location locals globals heap installed _
  obtain ⟨testExtension, testedStore, testEvaluation, testedHeap, testedInstalled, testFrame⟩ :=
    test_at tested truth compiled.conditionCompiled compiled.conditionConverted
      (Core.LocalLoop.conditionPrefix result location) locals globals heap installed
  obtain ⟨bodyExtension, bodyTarget, bodyStore, bodyRelated, bodyEvaluation, bodyHeap, bodyInstalled, bodyFrame⟩ :=
    statements_at bodyExecuted (progress_safe bodyContinues) compiled.bodyCompiled
      (Core.LocalLoop.bodyPrefix result location)
      (locals.extendWorld testExtension) globals testedHeap testedInstalled
  obtain ⟨bodyFlag, rfl⟩ := progress_value bodyRelated bodyContinues
  obtain ⟨postExtension, postTarget, finalStore, postRelated, postEvaluation, finalHeap, finalInstalled, postFrame⟩ :=
    statements_at postExecuted trivial compiled.postCompiled
      (Core.LocalLoop.postPrefix result location bodyFlag)
      ((locals.extendWorld testExtension).extendWorld bodyExtension) globals bodyHeap bodyInstalled
  simp only [Core.LocalLoop.postPrefix_length] at postEvaluation
  cases postRelated
  exact ⟨testExtension ++ bodyExtension ++ postExtension, _, finalStore, .fallthrough,
    Core.LocalLoop.loopBody_postBreak result (Core.Word.ofNatModulo 3) location bodyFlag
      testEvaluation bodyEvaluation postEvaluation,
    by simpa only [List.append_assoc] using finalHeap, finalInstalled,
    ClosuresPreserved.trans testFrame (ClosuresPreserved.trans bodyFrame postFrame)⟩

theorem post_stop {test : Expr} {post body : List Stmt}
    {initial testedState bodyState final : Semantics.State σ}
    {value : Semantics.Value} {bodyControl control : Semantics.Control}
    (tested : ExprSimulation signatures codes locations captured sourceEnvironment test initial (.value value) testedState)
    (truth : Semantics.condition? value = some true)
    (bodyExecuted : StatementsSimulation signatures codes locations captured sourceEnvironment body testedState bodyControl bodyState)
    (bodyContinues : bodyControl = .fallthrough ∨ bodyControl = .continuing)
    (postExecuted : StatementsSimulation signatures codes locations captured sourceEnvironment post bodyState control final)
    (stopped : (∃ value, control = .returned value) ∨ (∃ reason, control = .fault reason)) :
    LoopSimulation signatures codes locations captured sourceEnvironment test post body initial control final := by
  intro safe scope result loops compiled world mapping environment store location locals globals heap installed _
  rcases stopped with ⟨source, rfl⟩ | ⟨reason, rfl⟩
  · obtain ⟨testExtension, testedStore, testEvaluation, testedHeap, testedInstalled, testFrame⟩ :=
      test_at tested truth compiled.conditionCompiled compiled.conditionConverted
        (Core.LocalLoop.conditionPrefix result location) locals globals heap installed
    obtain ⟨bodyExtension, bodyTarget, bodyStore, bodyRelated, bodyEvaluation, bodyHeap, bodyInstalled, bodyFrame⟩ :=
      statements_at bodyExecuted (progress_safe bodyContinues) compiled.bodyCompiled
        (Core.LocalLoop.bodyPrefix result location)
        (locals.extendWorld testExtension) globals testedHeap testedInstalled
    obtain ⟨bodyFlag, rfl⟩ := progress_value bodyRelated bodyContinues
    obtain ⟨postExtension, postTarget, finalStore, postRelated, postEvaluation, finalHeap, finalInstalled, postFrame⟩ :=
      statements_at postExecuted safe compiled.postCompiled
        (Core.LocalLoop.postPrefix result location bodyFlag)
        ((locals.extendWorld testExtension).extendWorld bodyExtension) globals bodyHeap bodyInstalled
    simp only [Core.LocalLoop.postPrefix_length] at postEvaluation
    cases postRelated with
    | returned related =>
        exact ⟨testExtension ++ bodyExtension ++ postExtension, _, finalStore, .returned related,
          Core.LocalLoop.loopBody_postReturn result (Core.Word.ofNatModulo 3) location bodyFlag
            testEvaluation bodyEvaluation postEvaluation,
          by simpa only [List.append_assoc] using finalHeap, finalInstalled,
          ClosuresPreserved.trans testFrame (ClosuresPreserved.trans bodyFrame postFrame)⟩
  · cases safe

end Solcore.Frontend.RustHull.LoopDerivationCorrespondence

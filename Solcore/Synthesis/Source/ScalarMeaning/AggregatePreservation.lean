import Solcore.Synthesis.Source.ScalarMeaning.AggregateEquations
import Solcore.Synthesis.Source.ScalarMeaning.MutationPreservation

/-! Simulation lemmas for the actual `AggregateRenderer.render`: literals,
locals, cell reads and writes, `let`, operations, pairs, sum constructors and
helper calls. Operations print the call-graph formatting: raw opcode operands
are copied into fresh `word` temporaries first, and a copy is one more
rendering of the operand. The control forms are in `AggregateControl`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target)
open Solcore.Synthesis.Source.AggregateRenderer (Binding)
open Solcore.Synthesis.Core.Aggregates (Local initializerKind? infer?)

/-! ### Values -/

theorem AValue.ofScalar_iff {scalar : Target} {core : CoreValue} {source : Value} :
    AValue (ATarget.ofScalar scalar) core source ↔ Represents scalar core source := by
  cases scalar <;> exact Iff.rfl

theorem valueBinding_holds {target : ATarget} (valued : target ≠ .unit) (frames : Frames)
    (store : Solcore.Core.Store) (name : String) (core : CoreValue) :
    ABindingHolds frames store (valueBinding target name) core =
      ARepresents target core (frames.lookup name) := by
  cases target
  case unit => exact absurd rfl valued
  all_goals rfl

theorem toLocal_injective {first second : ATarget} (same : first.toLocal = second.toLocal) :
    first = second := by
  cases first <;> cases second <;> first | rfl | cases same

theorem atoLocal_scalarKind {target : ATarget} {scalar : Target}
    (same : target.toLocal = AggregateKinds.scalarKind scalar) :
    target = ATarget.ofScalar scalar := by
  cases target <;> cases scalar <;> first | rfl | cases same

theorem ofScalar_toLocal (scalar : Target) :
    (ATarget.ofScalar scalar).toLocal = AggregateKinds.scalarKind scalar := by
  cases scalar <;> rfl

theorem ARenderSpec.le {admits : Context → Prop} {expression : CoreExpr} {target : ATarget}
    {functions : List String} {bindings : List Binding} {indent first : Nat}
    {rendered : ARendered}
    (spec : ARenderSpec admits expression target functions bindings indent first rendered) :
    first ≤ rendered.nextId := by
  obtain ⟨_, _, le, _⟩ := spec
  exact le

/-! ### Call contexts -/

/-- An expression needs the alias context only if one of its parts does. -/
theorem AliasesReady.of_sub {expression sub : CoreExpr} {admits : Context → Prop}
    (ready : ∀ context, admits context → AliasesReady expression context)
    (uses : AggregateRenderer.usesOpcodeAliases sub = true →
      AggregateRenderer.usesOpcodeAliases expression = true) :
    ∀ context, admits context → AliasesReady sub context :=
  fun context admitted used => ready context admitted (uses used)

section

variable {admits : Context → Prop}

/-! ### Results -/

/-- The common tail of value expressions: after `statements`, the `tail`
declares the temporary `middle` with the value of the expression. -/
theorem aresult_simulates {expression : CoreExpr} {target : ATarget}
    {functions : List String} {bindings : List Binding} {first middle last : Nat}
    {statements tail : List Stmt}
    (fresh : ANamesFresh bindings first)
    (core : ∀ (context : Context) (environment : Solcore.Core.Environment)
      (store : Solcore.Core.Store) (scope : Scope) (outer : Frames),
      admits context → ABindingsAgree (scope :: outer) bindings environment store →
      ACellsDistinct bindings environment → bindings.length ≤ environment.length →
      MFunctionsAgree context functions (environment.drop bindings.length) →
      ∃ (coreValue : CoreValue) (value : Value) (store' : Solcore.Core.Store) (scope₁ : Scope)
        (outer₁ : Frames) (added : List String),
        Solcore.Core.Evaluates environment store expression.toCore coreValue store' ∧
        AValue target coreValue value ∧
        Stmt.execList context (scope :: outer) statements = some (scope₁ :: outer₁) ∧
        Stmt.execList context (scope₁ :: outer₁) tail =
          some (((temporary middle, value) :: scope₁) :: outer₁) ∧
        ABindingsAgree (scope₁ :: outer₁) bindings environment store' ∧
        AStoreFrame bindings environment store store' ∧
        (∀ name, ¬ ATempIn first middle name →
          (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
          Frames.lookup (scope₁ :: outer₁) name = Frames.lookup (scope :: outer) name) ∧
        Frames.shape outer₁ = Frames.shape outer ∧
        scope₁.names = added ++ scope.names ∧
        (∀ name ∈ added, ATempIn first middle name))
    (le : first ≤ middle) (high : middle < last) :
    ASimulates admits expression target functions bindings first last (statements ++ tail)
      (some (temporary middle)) := by
  intro context environment store scope outer admitted agree distinct lengthOk functionsOk
  obtain ⟨coreValue, value, store', scope₁, outer₁, added, evaluates, represents, exec, tailExec,
    agree₁, frame, keeps, shape, names, addedTemp⟩ :=
    core context environment store scope outer admitted agree distinct lengthOk functionsOk
  have temp : ATempIn first last (temporary middle) := aTempIn_temporary le high
  refine ⟨coreValue, store', (temporary middle, value) :: scope₁, outer₁,
    temporary middle :: added, evaluates, ?_, ?_, ?_, frame, ?_, shape, ?_, ?_⟩
  · simp only [Option.bind_some, Frames.lookup_declared, if_pos]
    exact ARepresents.of_value represents
  · rw [Stmt.execList_append, exec]
    simpa using tailExec
  · exact agree₁.declare (fresh.ne_temp temp) value
  · intro name notTemp notCell
    have different : temporary middle ≠ name := fun same => notTemp (same ▸ temp)
    rw [Frames.lookup_declared, if_neg different,
      keeps name (fun inRange => notTemp (aTempIn_mono inRange (Nat.le_refl _)
        (Nat.le_of_lt high))) notCell]
  · show temporary middle :: scope₁.names = (temporary middle :: added) ++ scope.names
    rw [names]
    rfl
  · intro name mem
    rcases List.mem_cons.mp mem with same | mem
    · exact same ▸ temp
    · exact aTempIn_mono (addedTemp name mem) (Nat.le_refl _) (Nat.le_of_lt high)

/-- The tail `let` of a value expression. -/
theorem let_exec {context : Context} {scope : Scope} {outer : Frames} {target : ATarget}
    {name : String} {initializer : Expr} {core : CoreValue} {value : Value}
    (initialized : initializer.eval context (scope :: outer) = some value)
    (represents : AValue target core value) :
    Stmt.execList context (scope :: outer) [.letDecl name target.localType initializer] =
      some (((name, value) :: scope) :: outer) := by
  simp [Stmt.execList, Stmt.exec, initialized, represents.admits, Frames.declare]

/-- An expression with no statements, whose value is already named. -/
theorem asimulates_nil {expression : CoreExpr} {target : ATarget}
    {functions : List String} {bindings : List Binding} {first : Nat}
    {valueName : Option String}
    (core : ∀ (environment : Solcore.Core.Environment) (store : Solcore.Core.Store)
      (scope : Scope) (outer : Frames),
      ABindingsAgree (scope :: outer) bindings environment store →
      ∃ coreValue : CoreValue,
        Solcore.Core.Evaluates environment store expression.toCore coreValue store ∧
        ARepresents target coreValue (valueName.bind (Frames.lookup (scope :: outer)))) :
    ASimulates admits expression target functions bindings first first [] valueName := by
  intro context environment store scope outer _ agree _ _ _
  obtain ⟨coreValue, evaluates, represents⟩ := core environment store scope outer agree
  exact ⟨coreValue, store, scope, outer, [], evaluates, represents, rfl, agree,
    AStoreFrame.refl _ _ _, fun _ _ _ => rfl, rfl, rfl, by simp⟩

/-- A value bound by one `let` whose initializer reads only bindings. -/
theorem aleaf_spec {expression : CoreExpr} {target : ATarget} {functions : List String}
    {bindings : List Binding} {indent first : Nat} {initializer : Expr}
    (fresh : ANamesFresh bindings first)
    (initializerNames : ∀ name ∈ initializer.identifiers,
      ∃ index, anameAt bindings index = some name)
    (evaluates : ∀ (context : Context) (environment : Solcore.Core.Environment)
      (store : Solcore.Core.Store) (frames : Frames),
      ABindingsAgree frames bindings environment store →
      ∃ (coreValue : CoreValue) (value : Value),
        Solcore.Core.Evaluates environment store expression.toCore coreValue store ∧
        initializer.eval context frames = some value ∧ AValue target coreValue value) :
    ARenderSpec admits expression target functions bindings indent first
      ⟨Stmt.lines indent (.letDecl (temporary first) target.localType initializer),
        some (temporary first), first + 1⟩ := by
  unfold ARenderSpec
  dsimp only
  refine ⟨[.letDecl (temporary first) target.localType initializer], by simp [Stmt.listLines],
    Nat.le_succ _, ?_, ?_, ?_⟩
  · intro name same
    cases same
    exact Or.inr ⟨first, rfl, Nat.le_refl _, Nat.lt_succ_self _⟩
  · intro name mem
    simp only [Stmt.listIdentifiers, Stmt.identifiers, List.append_nil, List.mem_cons] at mem
    rcases mem with same | mem
    · exact Or.inr (Or.inr (Or.inl (same ▸ aTempIn_temporary (Nat.le_refl _)
        (Nat.lt_succ_self _))))
    · exact Or.inl (initializerNames name mem)
  · have simulates := aresult_simulates (admits := admits) (expression := expression)
      (functions := functions) (statements := [])
      (tail := [.letDecl (temporary first) target.localType initializer]) fresh
      (fun context environment store scope outer _ agree _ _ _ => by
        obtain ⟨coreValue, value, evaluates', initialized, represents⟩ :=
          evaluates context environment store (scope :: outer) agree
        exact ⟨coreValue, value, store, scope, outer, [], evaluates', represents, rfl,
          let_exec initialized represents, agree, AStoreFrame.refl _ _ _, fun _ _ _ => rfl, rfl,
          rfl, by simp⟩)
      (Nat.le_refl first) (Nat.lt_succ_self first)
    rw [List.nil_append] at simulates
    exact simulates

/-- One operand followed by a fresh temporary bound to `initializer`, which
reads the operand's value name. The final step may run a helper, which
allocates only new store locations. -/
theorem aoneResult_spec {expression operand : CoreExpr} {operandTarget target : ATarget}
    {functions : List String} {bindings : List Binding} {indent first : Nat}
    {operandRendered : ARendered} {operandValue : String} {initializer : Expr}
    (operandValued : operandTarget ≠ .unit) (fresh : ANamesFresh bindings first)
    (spec : ARenderSpec admits operand operandTarget functions bindings indent first
      operandRendered)
    (named : operandRendered.value = some operandValue)
    (initializerNames : ∀ name ∈ initializer.identifiers,
      name = operandValue ∨ name ∈ functions ∨ name ∈ primitiveCallees)
    (combine : ∀ (context : Context) (environment : Solcore.Core.Environment)
      (store store₁ : Solcore.Core.Store) (operandCore : CoreValue) (frames : Frames)
      (source : Value),
      admits context → bindings.length ≤ environment.length →
      MFunctionsAgree context functions (environment.drop bindings.length) →
      Solcore.Core.Evaluates environment store operand.toCore operandCore store₁ →
      frames.lookup operandValue = some source → AValue operandTarget operandCore source →
      ∃ (coreResult : CoreValue) (sourceResult : Value) (store₂ : Solcore.Core.Store),
        Solcore.Core.Evaluates environment store expression.toCore coreResult store₂ ∧
        store₁.length ≤ store₂.length ∧
        (∀ location, location < store₁.length →
          store₂.read? location = store₁.read? location) ∧
        initializer.eval context frames = some sourceResult ∧
        AValue target coreResult sourceResult) :
    ARenderSpec admits expression target functions bindings indent first
      ⟨operandRendered.lines ++ Stmt.lines indent
          (.letDecl (temporary operandRendered.nextId) target.localType initializer),
        some (temporary operandRendered.nextId), operandRendered.nextId + 1⟩ := by
  obtain ⟨statements, lines, le, valueName, uses, simulates⟩ := spec
  unfold ARenderSpec
  dsimp only
  refine ⟨statements ++ [.letDecl (temporary operandRendered.nextId) target.localType
      initializer], ?_, by omega, ?_, ?_, ?_⟩
  · simp only [Stmt.listLines_append, lines, Stmt.listLines, List.append_nil]
  · intro name same
    cases same
    exact Or.inr ⟨operandRendered.nextId, rfl, le, Nat.lt_succ_self _⟩
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, List.append_nil, List.mem_cons] at mem
    rcases mem with mem | same | mem
    · exact (uses name mem).mono (Nat.le_refl _) (Nat.le_succ _)
    · exact Or.inr (Or.inr (Or.inl (same ▸ aTempIn_temporary le (Nat.lt_succ_self _))))
    · rcases initializerNames name mem with same | mem | called
      · subst same
        exact (valueName _ named).uses.mono (Nat.le_refl _) (Nat.le_succ _)
      · exact Or.inr (Or.inl mem)
      · exact Or.inr (Or.inr (Or.inr called))
  · refine aresult_simulates fresh (fun context environment store scope outer admitted agree
      distinct lengthOk functionsOk => ?_) le (Nat.lt_succ_self _)
    obtain ⟨core, store₁, scope₁, outer₁, added₁, evaluates, represents, exec, agree₁, frame₁,
      keeps₁, shape₁, names₁, addedTemp₁⟩ :=
      simulates context environment store scope outer admitted agree distinct lengthOk
        functionsOk
    rw [named, Option.bind_some] at represents
    obtain ⟨source, lookup, operandValue'⟩ := represents.value operandValued
    obtain ⟨coreResult, sourceResult, store₂, evaluates', grows, keepsStore, initialized,
      resultValue⟩ :=
      combine context environment store store₁ core _ source admitted lengthOk functionsOk
        evaluates lookup operandValue'
    refine ⟨coreResult, sourceResult, store₂, scope₁, outer₁, added₁, evaluates', resultValue,
      exec, let_exec initialized resultValue, ?_, ?_, keeps₁, shape₁, names₁, addedTemp₁⟩
    · exact agree₁.transfer (fun _ _ _ => rfl) fun _ location isCell =>
        keepsStore location (agree₁.cell_lt isCell)
    · exact frame₁.trans ⟨grows, fun location inBounds _ => keepsStore location inBounds⟩

/-- Two Word operands, left to right, followed by a fresh temporary bound to
`initializer`, which reads both value names. -/
theorem atwoResult_spec {expression left right : CoreExpr} {target : ATarget}
    {functions : List String} {bindings : List Binding} {indent first : Nat}
    {leftRendered rightRendered : ARendered} {leftValue rightValue : String}
    {initializer : Expr}
    (fresh : ANamesFresh bindings first) (distinct : ANamesDistinct bindings)
    (leftSpec : ARenderSpec admits left .word functions bindings indent first leftRendered)
    (leftNamed : leftRendered.value = some leftValue)
    (rightSpec : ARenderSpec admits right .word functions bindings indent leftRendered.nextId
      rightRendered)
    (rightNamed : rightRendered.value = some rightValue)
    (initializerNames : ∀ name ∈ initializer.identifiers,
      name = leftValue ∨ name = rightValue ∨ name ∈ primitiveCallees)
    (combine : ∀ (context : Context) (environment : Solcore.Core.Environment)
      (store store₁ store₂ : Solcore.Core.Store) (leftWord rightWord : Solcore.Core.Word)
      (frames : Frames),
      admits context →
      Solcore.Core.Evaluates environment store left.toCore (.word leftWord) store₁ →
      Solcore.Core.Evaluates environment store₁ right.toCore (.word rightWord) store₂ →
      frames.lookup leftValue = some (.word leftWord.val) →
      frames.lookup rightValue = some (.word rightWord.val) →
      ∃ (coreResult : CoreValue) (sourceResult : Value),
        Solcore.Core.Evaluates environment store expression.toCore coreResult store₂ ∧
        initializer.eval context frames = some sourceResult ∧
        AValue target coreResult sourceResult) :
    ARenderSpec admits expression target functions bindings indent first
      ⟨leftRendered.lines ++ rightRendered.lines ++ Stmt.lines indent
          (.letDecl (temporary rightRendered.nextId) target.localType initializer),
        some (temporary rightRendered.nextId), rightRendered.nextId + 1⟩ := by
  obtain ⟨leftStatements, leftLines, leftLe, leftValueName, leftUses, leftSimulates⟩ := leftSpec
  obtain ⟨rightStatements, rightLines, rightLe, rightValueName, rightUses, rightSimulates⟩ :=
    rightSpec
  unfold ARenderSpec
  dsimp only
  refine ⟨leftStatements ++ rightStatements ++ [.letDecl (temporary rightRendered.nextId)
      target.localType initializer], ?_, by omega, ?_, ?_, ?_⟩
  · simp only [Stmt.listLines_append, leftLines, rightLines, Stmt.listLines, List.append_nil]
  · intro name same
    cases same
    exact Or.inr ⟨rightRendered.nextId, rfl, by omega, Nat.lt_succ_self _⟩
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, List.append_nil, List.mem_cons] at mem
    rcases mem with (mem | mem) | same | mem
    · exact (leftUses name mem).mono (Nat.le_refl _) (by omega)
    · exact (rightUses name mem).mono leftLe (by omega)
    · exact Or.inr (Or.inr (Or.inl (same ▸ aTempIn_temporary (by omega) (Nat.lt_succ_self _))))
    · rcases initializerNames name mem with same | same | called
      · subst same
        exact (leftValueName _ leftNamed).uses.mono (Nat.le_refl _) (by omega)
      · subst same
        exact (rightValueName _ rightNamed).uses.mono leftLe (by omega)
      · exact Or.inr (Or.inr (Or.inr called))
  · refine aresult_simulates fresh (fun context environment store scope outer admitted agree
      distinctCells lengthOk functionsOk => ?_) (by omega) (Nat.lt_succ_self _)
    obtain ⟨leftCore, store₁, scope₁, outer₁, added₁, leftEvaluates, leftRepresents,
      leftExec, agree₁, frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
      leftSimulates context environment store scope outer admitted agree distinctCells
        lengthOk functionsOk
    obtain ⟨rightCore, store₂, scope₂, outer₂, added₂, rightEvaluates, rightRepresents,
      rightExec, agree₂, frame₂, keeps₂, shape₂, names₂, addedTemp₂⟩ :=
      rightSimulates context environment store₁ scope₁ outer₁ admitted agree₁ distinctCells
        lengthOk functionsOk
    rw [leftNamed, Option.bind_some] at leftRepresents
    rw [rightNamed, Option.bind_some] at rightRepresents
    obtain ⟨_, leftLookup, leftWord, rfl, rfl⟩ := leftRepresents
    obtain ⟨_, rightLookup, rightWord, rfl, rfl⟩ := rightRepresents
    obtain ⟨leftSurvivesTemp, leftSurvivesCell⟩ :=
      (leftValueName leftValue leftNamed).survives (last := rightRendered.nextId) fresh
        distinct leftLe
    have leftLookup₂ : Frames.lookup (scope₂ :: outer₂) leftValue =
        some (.word leftWord.val) := by
      rw [keeps₂ leftValue leftSurvivesTemp leftSurvivesCell]
      exact leftLookup
    obtain ⟨coreResult, sourceResult, evaluates, initialized, resultValue⟩ :=
      combine context environment store store₁ store₂ leftWord rightWord _ admitted
        leftEvaluates rightEvaluates leftLookup₂ rightLookup
    refine ⟨coreResult, sourceResult, store₂, scope₂, outer₂, added₂ ++ added₁, evaluates,
      resultValue, ?_, let_exec initialized resultValue, agree₂, frame₁.trans frame₂, ?_,
      shape₂.trans shape₁, ?_, ?_⟩
    · rw [Stmt.execList_append, leftExec]
      simpa using rightExec
    · intro name notTemp notCell
      rw [keeps₂ name (fun temp => notTemp (aTempIn_mono temp leftLe (Nat.le_refl _))) notCell,
        keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) rightLe)) notCell]
    · rw [names₂, names₁]
      simp
    · intro name mem
      rcases List.mem_append.mp mem with mem | mem
      · exact aTempIn_mono (addedTemp₂ name mem) leftLe (Nat.le_refl _)
      · exact aTempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) rightLe

/-- Three Word operands, left to right, followed by a fresh temporary bound to
`initializer`, which reads the three value names. -/
theorem athreeResult_spec {expression one two three : CoreExpr} {target : ATarget}
    {functions : List String} {bindings : List Binding} {indent first : Nat}
    {oneRendered twoRendered threeRendered : ARendered} {oneValue twoValue threeValue : String}
    {initializer : Expr}
    (fresh : ANamesFresh bindings first) (distinct : ANamesDistinct bindings)
    (oneSpec : ARenderSpec admits one .word functions bindings indent first oneRendered)
    (oneNamed : oneRendered.value = some oneValue)
    (twoSpec : ARenderSpec admits two .word functions bindings indent oneRendered.nextId
      twoRendered)
    (twoNamed : twoRendered.value = some twoValue)
    (threeSpec : ARenderSpec admits three .word functions bindings indent twoRendered.nextId
      threeRendered)
    (threeNamed : threeRendered.value = some threeValue)
    (initializerNames : ∀ name ∈ initializer.identifiers,
      name = oneValue ∨ name = twoValue ∨ name = threeValue ∨ name ∈ primitiveCallees)
    (combine : ∀ (context : Context) (environment : Solcore.Core.Environment)
      (store store₁ store₂ store₃ : Solcore.Core.Store)
      (oneWord twoWord threeWord : Solcore.Core.Word) (frames : Frames),
      admits context →
      Solcore.Core.Evaluates environment store one.toCore (.word oneWord) store₁ →
      Solcore.Core.Evaluates environment store₁ two.toCore (.word twoWord) store₂ →
      Solcore.Core.Evaluates environment store₂ three.toCore (.word threeWord) store₃ →
      frames.lookup oneValue = some (.word oneWord.val) →
      frames.lookup twoValue = some (.word twoWord.val) →
      frames.lookup threeValue = some (.word threeWord.val) →
      ∃ (coreResult : CoreValue) (sourceResult : Value),
        Solcore.Core.Evaluates environment store expression.toCore coreResult store₃ ∧
        initializer.eval context frames = some sourceResult ∧
        AValue target coreResult sourceResult) :
    ARenderSpec admits expression target functions bindings indent first
      ⟨oneRendered.lines ++ twoRendered.lines ++ threeRendered.lines ++ Stmt.lines indent
          (.letDecl (temporary threeRendered.nextId) target.localType initializer),
        some (temporary threeRendered.nextId), threeRendered.nextId + 1⟩ := by
  obtain ⟨oneStatements, oneLines, oneLe, oneValueName, oneUses, oneSimulates⟩ := oneSpec
  obtain ⟨twoStatements, twoLines, twoLe, twoValueName, twoUses, twoSimulates⟩ := twoSpec
  obtain ⟨threeStatements, threeLines, threeLe, threeValueName, threeUses, threeSimulates⟩ :=
    threeSpec
  unfold ARenderSpec
  dsimp only
  refine ⟨oneStatements ++ twoStatements ++ threeStatements ++
      [.letDecl (temporary threeRendered.nextId) target.localType initializer], ?_,
    by omega, ?_, ?_, ?_⟩
  · simp only [Stmt.listLines_append, oneLines, twoLines, threeLines, Stmt.listLines,
      List.append_nil]
  · intro name same
    cases same
    exact Or.inr ⟨threeRendered.nextId, rfl, by omega, Nat.lt_succ_self _⟩
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, List.append_nil, List.mem_cons] at mem
    rcases mem with ((mem | mem) | mem) | same | mem
    · exact (oneUses name mem).mono (Nat.le_refl _) (by omega)
    · exact (twoUses name mem).mono oneLe (by omega)
    · exact (threeUses name mem).mono (by omega) (by omega)
    · exact Or.inr (Or.inr (Or.inl (same ▸ aTempIn_temporary (by omega) (Nat.lt_succ_self _))))
    · rcases initializerNames name mem with same | same | same | called
      · subst same
        exact (oneValueName _ oneNamed).uses.mono (Nat.le_refl _) (by omega)
      · subst same
        exact (twoValueName _ twoNamed).uses.mono oneLe (by omega)
      · subst same
        exact (threeValueName _ threeNamed).uses.mono (by omega) (by omega)
      · exact Or.inr (Or.inr (Or.inr called))
  · refine aresult_simulates fresh (fun context environment store scope outer admitted agree
      distinctCells lengthOk functionsOk => ?_) (by omega) (Nat.lt_succ_self _)
    obtain ⟨oneCore, store₁, scope₁, outer₁, added₁, oneEvaluates, oneRepresents, oneExec,
      agree₁, frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
      oneSimulates context environment store scope outer admitted agree distinctCells lengthOk
        functionsOk
    obtain ⟨twoCore, store₂, scope₂, outer₂, added₂, twoEvaluates, twoRepresents, twoExec,
      agree₂, frame₂, keeps₂, shape₂, names₂, addedTemp₂⟩ :=
      twoSimulates context environment store₁ scope₁ outer₁ admitted agree₁ distinctCells
        lengthOk functionsOk
    obtain ⟨threeCore, store₃, scope₃, outer₃, added₃, threeEvaluates, threeRepresents,
      threeExec, agree₃, frame₃, keeps₃, shape₃, names₃, addedTemp₃⟩ :=
      threeSimulates context environment store₂ scope₂ outer₂ admitted agree₂ distinctCells
        lengthOk functionsOk
    rw [oneNamed, Option.bind_some] at oneRepresents
    rw [twoNamed, Option.bind_some] at twoRepresents
    rw [threeNamed, Option.bind_some] at threeRepresents
    obtain ⟨_, oneLookup, oneWord, rfl, rfl⟩ := oneRepresents
    obtain ⟨_, twoLookup, twoWord, rfl, rfl⟩ := twoRepresents
    obtain ⟨_, threeLookup, threeWord, rfl, rfl⟩ := threeRepresents
    obtain ⟨oneSurvivesTwo, oneNotCell⟩ :=
      (oneValueName oneValue oneNamed).survives (last := twoRendered.nextId) fresh distinct oneLe
    obtain ⟨oneSurvivesThree, _⟩ :=
      ((oneValueName oneValue oneNamed).mono (Nat.le_refl _) twoLe).survives
        (last := threeRendered.nextId) fresh distinct (Nat.le_trans oneLe twoLe)
    obtain ⟨twoSurvivesThree, twoNotCell⟩ :=
      (twoValueName twoValue twoNamed).survives (last := threeRendered.nextId)
        (fresh.mono oneLe) distinct twoLe
    have oneLookup₃ : Frames.lookup (scope₃ :: outer₃) oneValue = some (.word oneWord.val) := by
      rw [keeps₃ oneValue oneSurvivesThree oneNotCell,
        keeps₂ oneValue oneSurvivesTwo oneNotCell]
      exact oneLookup
    have twoLookup₃ : Frames.lookup (scope₃ :: outer₃) twoValue = some (.word twoWord.val) := by
      rw [keeps₃ twoValue twoSurvivesThree twoNotCell]
      exact twoLookup
    obtain ⟨coreResult, sourceResult, evaluates, initialized, resultValue⟩ :=
      combine context environment store store₁ store₂ store₃ oneWord twoWord threeWord _ admitted
        oneEvaluates twoEvaluates threeEvaluates oneLookup₃ twoLookup₃ threeLookup
    refine ⟨coreResult, sourceResult, store₃, scope₃, outer₃, added₃ ++ added₂ ++ added₁,
      evaluates, resultValue, ?_, let_exec initialized resultValue, agree₃,
      (frame₁.trans frame₂).trans frame₃, ?_, (shape₃.trans shape₂).trans shape₁, ?_, ?_⟩
    · rw [Stmt.execList_append, Stmt.execList_append, oneExec]
      simp [twoExec, threeExec]
    · intro name notTemp notCell
      rw [keeps₃ name (fun temp => notTemp (aTempIn_mono temp (by omega) (Nat.le_refl _)))
          notCell,
        keeps₂ name (fun temp => notTemp (aTempIn_mono temp oneLe (by omega))) notCell,
        keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) (by omega)))
          notCell]
    · rw [names₃, names₂, names₁]
      simp
    · intro name mem
      simp only [List.mem_append] at mem
      rcases mem with (mem | mem) | mem
      · exact aTempIn_mono (addedTemp₃ name mem) (by omega) (Nat.le_refl _)
      · exact aTempIn_mono (addedTemp₂ name mem) oneLe (by omega)
      · exact aTempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) (by omega)

/-- A snapshot of a rendered Word operand is one more rendering of it. -/
theorem asnapshot_spec {expression : CoreExpr} {functions : List String}
    {bindings : List Binding} {indent first : Nat} {value : ScalarRenderer.Rendered}
    (fresh : ANamesFresh bindings first)
    (spec : ARenderSpec admits expression .word functions bindings indent first
      (ARendered.ofScalar value)) :
    ARenderSpec admits expression .word functions bindings indent first
      (ARendered.ofScalar (snapshotOf indent value)) := by
  have result := aoneResult_spec (expression := expression) (operand := expression)
    (target := .word) (initializer := .name value.value) (by simp) fresh spec rfl
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
      exact Or.inl mem)
    (fun context environment store store₁ operandCore frames source _ _ _ evaluates lookup
      represents => ⟨operandCore, source, store₁, evaluates, Nat.le_refl _, fun _ _ => rfl,
        by simpa [Expr.eval] using lookup, represents⟩)
  exact result

/-! ### Literals, locals and cell reads -/

theorem aRenderIH_word (value : Solcore.Core.Word) : ARenderIH (.word value) := by
  intro admits _ functions target bindings indent first rendered accepted equation fresh _
  have targetWord : target = .word := by
    cases target <;> first | rfl | cases accepted
  subst targetWord
  rw [AggregateEquations.word] at equation
  cases equation
  exact aleaf_spec (target := .word) (initializer := .number value.val) fresh
    (fun _ mem => by simp [Expr.identifiers] at mem)
    (fun _ _ store _ _ => ⟨.word value, .word value.val, by
      simp only [Solcore.Core.Wire.Expr.toCore]; exact .word,
      by simp [Expr.eval, word_lt_modulus], value, rfl, rfl⟩)

theorem aRenderIH_bool (value : Bool) : ARenderIH (.bool value) := by
  intro admits _ functions target bindings indent first rendered accepted equation fresh _
  have targetBool : target = .bool := by
    cases target <;> first | rfl | cases accepted
  subst targetBool
  rw [AggregateEquations.bool] at equation
  cases equation
  exact aleaf_spec (target := .bool) (initializer := .bool value) fresh
    (fun _ mem => by simp [Expr.identifiers] at mem)
    (fun _ _ store _ _ => ⟨.bool value, .bool value, by
      simp only [Solcore.Core.Wire.Expr.toCore]; exact .bool, rfl, value, rfl, rfl⟩)

theorem aRenderIH_unit : ARenderIH .unit := by
  intro admits _ functions target bindings indent first rendered accepted equation _ _
  have targetUnit : target = .unit := by
    cases target <;> first | rfl | cases accepted
  subst targetUnit
  rw [AggregateEquations.unit] at equation
  cases equation
  refine ⟨[], rfl, Nat.le_refl _, (fun _ same => by cases same),
    (by simp [Stmt.listIdentifiers]), asimulates_nil fun _ _ _ _ _ => ⟨.unit, ?_, rfl⟩⟩
  simp only [Solcore.Core.Wire.Expr.toCore]
  exact .unit

theorem aRenderIH_var (index : Nat) : ARenderIH (.var index) := by
  intro admits _ functions target bindings indent first rendered accepted equation _ _
  obtain ⟨kindFound, _⟩ := AggregateKinds.var accepted
  rw [List.getElem?_map] at kindFound
  rcases AggregateEquations.var_ok equation with ⟨name, kind, valued, found, rfl⟩ | ⟨found, rfl⟩
  · rw [found] at kindFound
    simp only [Option.map_some, Option.some.injEq] at kindFound
    rw [valueBinding_kind valued] at kindFound
    have sameTarget := toLocal_injective kindFound
    subst sameTarget
    refine ⟨[], rfl, Nat.le_refl _, ?_, by simp [Stmt.listIdentifiers], ?_⟩
    · intro value same
      cases same
      exact Or.inl ⟨index, kind, valued, found⟩
    · refine asimulates_nil fun environment store scope outer agree => ?_
      obtain ⟨core, inEnvironment, holds⟩ := agree index _ found
      rw [valueBinding_holds valued] at holds
      refine ⟨core, ?_, by simpa using holds⟩
      simp only [Solcore.Core.Wire.Expr.toCore]
      exact .var inEnvironment
  · rw [found] at kindFound
    simp only [Option.map_some, Option.some.injEq] at kindFound
    have targetUnit : target = .unit := by
      cases target <;> first | rfl | cases kindFound
    subst targetUnit
    refine ⟨[], rfl, Nat.le_refl _, (fun _ same => by cases same),
      (by simp [Stmt.listIdentifiers]), ?_⟩
    refine asimulates_nil fun environment store scope outer agree => ?_
    obtain ⟨core, inEnvironment, same⟩ := agree index _ found
    refine ⟨core, ?_, same⟩
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .var inEnvironment

theorem aRenderIH_loadCell (index : Nat) : ARenderIH (.loadCell (.var index)) := by
  intro admits _ functions target bindings indent first rendered accepted equation fresh _
  obtain ⟨cellKind, resultWord⟩ := AggregateKinds.loadCell accepted
  have targetWord : target = .word := by
    cases target <;> first | rfl | cases resultWord
  subst targetWord
  obtain ⟨name, found, rfl⟩ := AggregateEquations.loadCell_ok equation
  exact aleaf_spec (target := .word) (initializer := .name name) fresh
    (fun other mem => by
      simp only [Expr.identifiers, List.mem_singleton] at mem
      subst mem
      exact ⟨index, by rw [anameAt_of_getElem? found]; rfl⟩)
    (fun _ environment store frames agree => by
      obtain ⟨core, inEnvironment, elementType, location, word, rfl, read, lookup⟩ :=
        agree index _ found
      refine ⟨.word word, .word word.val, ?_, by simpa [Expr.eval] using lookup, word, rfl, rfl⟩
      simp only [Solcore.Core.Wire.Expr.toCore]
      exact .loadCell (.var inEnvironment) read)

/-! ### Operations, pairs, sum constructors and helper calls -/

theorem aRenderIH_unarySource {op : Solcore.Core.Wire.UnaryOp} {sourceOp : UnaryOp}
    {operand : CoreExpr} (selected : sourceUnary? op = some sourceOp)
    (operandIH : ARenderIH operand) : ARenderIH (.unary op operand) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨_, operandKind, resultKind⟩ := AggregateKinds.unary accepted
  have targetEq := atoLocal_scalarKind resultKind
  subst targetEq
  rw [AggregateEquations.unary _ _ _ _ selected] at equation
  obtain ⟨operandRendered, operandEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨named, ofScalar⟩ := ascalarValue_ok valueEquation
  cases equation
  have operandTarget : (if op == .boolNot then (.bool : ATarget) else .word) =
      ATarget.ofScalar (Target.unaryOperand op) := by
    cases op <;> simp_all [sourceUnary?] <;> rfl
  rw [operandTarget] at operandEquation
  have spec := operandIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions (ATarget.ofScalar (Target.unaryOperand op)) bindings indent first operandRendered
    (by rw [ofScalar_toLocal]; exact operandKind) operandEquation fresh distinct
  rw [← ofScalar] at spec
  rw [← ATarget.ofScalar_localType]
  refine aoneResult_spec (ATarget.ofScalar_ne_unit _) fresh spec rfl
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
      exact Or.inl mem) ?_
  intro context environment store store₁ operandCore frames source _ _ _ evaluates lookup
    represents
  have scalarRepresents := AValue.ofScalar_iff.mp represents
  rw [unaryOperand_eq selected] at scalarRepresents
  obtain ⟨coreResult, sourceResult, coreApply, sourceApply, resultRepresents⟩ :=
    unary_agree selected scalarRepresents
  refine ⟨coreResult, sourceResult, store₁, ?_, Nat.le_refl _, fun _ _ => rfl, ?_,
    AValue.ofScalar_iff.mpr resultRepresents⟩
  · simp only [Solcore.Core.Wire.Expr.toCore]
    exact .unary evaluates coreApply
  · simp [Expr.eval, lookup, sourceApply]

theorem aRenderIH_clz {operand : CoreExpr} (operandIH : ARenderIH operand) :
    ARenderIH (.unary .wordClz operand) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨_, operandKind, resultKind⟩ := AggregateKinds.unary accepted
  have targetEq := atoLocal_scalarKind resultKind
  subst targetEq
  rw [show ATarget.ofScalar (Target.unaryResult .wordClz) = .word from rfl,
    AggregateEquations.clz] at equation
  obtain ⟨operandRendered, operandEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨named, ofScalar⟩ := ascalarValue_ok valueEquation
  cases equation
  have spec := operandIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .word bindings indent first operandRendered operandKind operandEquation fresh
    distinct
  rw [← ofScalar] at spec
  have snapshot := asnapshot_spec fresh spec
  refine aoneResult_spec (target := .word) (by simp) fresh snapshot rfl
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with same | same
      · exact Or.inr (Or.inr (same ▸ by simp [primitiveCallees, primitiveAliases]))
      · exact Or.inl same) ?_
  intro context environment store store₁ operandCore frames source admitted _ _ evaluates
    lookup represents
  have primitive : PrimitiveContext context :=
    ready context admitted rfl
  obtain ⟨word, rfl, rfl⟩ := represents
  refine ⟨.word word.clz, .word (Evm.clz word.val), store₁, ?_, Nat.le_refl _,
    fun _ _ => rfl, ?_, word.clz, rfl, by rw [evm_clz]⟩
  · simp only [Solcore.Core.Wire.Expr.toCore]
    exact .unary evaluates rfl
  · simp only [snapshotOf] at lookup
    simp [Expr.eval, lookup, primitive.reaches (opcode := "clz") (alias := "sc_clz")
      (by decide), opcodeMeaning]

theorem aRenderIH_binarySource {op : Solcore.Core.Wire.BinaryOp} {sourceOp : BinaryOp}
    {left right : CoreExpr} (selected : sourceBinary? op = some sourceOp)
    (leftIH : ARenderIH left) (rightIH : ARenderIH right) :
    ARenderIH (.binary op left right) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨_, leftKind, rightKind, resultKind⟩ := AggregateKinds.binary accepted
  have targetEq := atoLocal_scalarKind resultKind
  subst targetEq
  rw [AggregateEquations.binary _ _ _ _ _ selected] at equation
  obtain ⟨leftRendered, leftEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨leftValue, leftValueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightRendered, rightEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightValue, rightValueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨leftNamed, leftOfScalar⟩ := ascalarValue_ok leftValueEquation
  obtain ⟨rightNamed, rightOfScalar⟩ := ascalarValue_ok rightValueEquation
  cases equation
  have leftSpec := leftIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .word bindings indent first leftRendered leftKind leftEquation fresh distinct
  rw [← leftOfScalar] at leftSpec
  have rightSpec := rightIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .word bindings indent leftValue.nextId rightRendered rightKind rightEquation
    (fresh.mono leftSpec.le) distinct
  rw [← rightOfScalar] at rightSpec
  rw [← ATarget.ofScalar_localType]
  refine atwoResult_spec fresh distinct leftSpec rfl rightSpec rfl
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_append, List.mem_singleton] at mem
      rcases mem with same | same
      · exact Or.inl same
      · exact Or.inr (Or.inl same)) ?_
  intro context environment store store₁ store₂ leftWord rightWord frames _ leftEvaluates
    rightEvaluates leftLookup rightLookup
  obtain ⟨coreResult, sourceResult, coreApply, sourceApply, resultRepresents⟩ :=
    binary_agree selected leftWord rightWord
  refine ⟨coreResult, sourceResult, ?_, ?_, AValue.ofScalar_iff.mpr resultRepresents⟩
  · simp only [Solcore.Core.Wire.Expr.toCore]
    exact .binary leftEvaluates rightEvaluates coreApply
  · simp [Expr.eval, leftLookup, rightLookup, sourceApply]

theorem primitiveBinary_uses {op : Solcore.Core.Wire.BinaryOp}
    {build : String → String → Expr} (selected : primitiveBinary? op = some build)
    (left right : CoreExpr) :
    AggregateRenderer.usesOpcodeAliases (.binary op left right) = true := by
  cases op <;> simp only [primitiveBinary?, reduceCtorEq] at selected <;> rfl

theorem aRenderIH_binaryPrimitive {op : Solcore.Core.Wire.BinaryOp}
    {build : String → String → Expr} {left right : CoreExpr}
    (selected : primitiveBinary? op = some build)
    (leftIH : ARenderIH left) (rightIH : ARenderIH right) :
    ARenderIH (.binary op left right) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨_, leftKind, rightKind, resultKind⟩ := AggregateKinds.binary accepted
  have targetEq := atoLocal_scalarKind resultKind
  subst targetEq
  rw [AggregateEquations.binary_primitive _ _ _ _ _ selected] at equation
  obtain ⟨leftRendered, leftEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨leftValue, leftValueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightRendered, rightEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightValue, rightValueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨leftNamed, leftOfScalar⟩ := ascalarValue_ok leftValueEquation
  obtain ⟨rightNamed, rightOfScalar⟩ := ascalarValue_ok rightValueEquation
  cases equation
  have leftSpec := leftIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .word bindings indent first leftRendered leftKind leftEquation fresh distinct
  rw [← leftOfScalar] at leftSpec
  have leftSnapshot := asnapshot_spec fresh leftSpec
  have rightSpec := rightIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .word bindings indent (leftValue.nextId + 1) rightRendered rightKind rightEquation
    (fresh.mono leftSnapshot.le) distinct
  rw [← rightOfScalar] at rightSpec
  have rightSnapshot := asnapshot_spec (fresh.mono leftSnapshot.le) rightSpec
  rw [← ATarget.ofScalar_localType]
  refine atwoResult_spec fresh distinct leftSnapshot rfl rightSnapshot rfl
    (primitiveBinary_names selected _ _) ?_
  intro context environment store store₁ store₂ leftWord rightWord frames admitted
    leftEvaluates rightEvaluates leftLookup rightLookup
  have primitive : PrimitiveContext context :=
    ready context admitted (primitiveBinary_uses selected left right)
  obtain ⟨coreResult, sourceResult, coreApply, sourceApply, resultRepresents⟩ :=
    primitiveBinary_agree selected context frames _ _ leftWord rightWord primitive leftLookup
      rightLookup
  refine ⟨coreResult, sourceResult, ?_, sourceApply, AValue.ofScalar_iff.mpr resultRepresents⟩
  simp only [Solcore.Core.Wire.Expr.toCore]
  exact .binary leftEvaluates rightEvaluates coreApply

theorem aRenderIH_ternary {op : Solcore.Core.Wire.TernaryOp} {one two three : CoreExpr}
    (oneIH : ARenderIH one) (twoIH : ARenderIH two) (threeIH : ARenderIH three) :
    ARenderIH (.ternary op one two three) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨oneKind, twoKind, threeKind, resultWord⟩ := AggregateKinds.ternary accepted
  have targetWord : target = .word := by
    cases target <;> first | rfl | cases resultWord
  subst targetWord
  rw [AggregateEquations.ternary] at equation
  obtain ⟨oneRendered, oneEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨oneValue, oneValueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨twoRendered, twoEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨twoValue, twoValueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨threeRendered, threeEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨threeValue, threeValueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨_, oneOfScalar⟩ := ascalarValue_ok oneValueEquation
  obtain ⟨_, twoOfScalar⟩ := ascalarValue_ok twoValueEquation
  obtain ⟨_, threeOfScalar⟩ := ascalarValue_ok threeValueEquation
  cases equation
  have uses : ∀ sub, sub = one ∨ sub = two ∨ sub = three →
      ∀ context, admits context → AliasesReady sub context := by
    intro sub _
    exact AliasesReady.of_sub ready fun _ => rfl
  have oneSpec := oneIH admits (uses one (Or.inl rfl)) functions .word bindings indent first
    oneRendered oneKind oneEquation fresh distinct
  rw [← oneOfScalar] at oneSpec
  have oneSnapshot := asnapshot_spec fresh oneSpec
  have twoSpec := twoIH admits (uses two (Or.inr (Or.inl rfl))) functions .word bindings indent
    (oneValue.nextId + 1) twoRendered twoKind twoEquation (fresh.mono oneSnapshot.le) distinct
  rw [← twoOfScalar] at twoSpec
  have twoSnapshot := asnapshot_spec (fresh.mono oneSnapshot.le) twoSpec
  have threeSpec := threeIH admits (uses three (Or.inr (Or.inr rfl))) functions .word bindings
    indent (twoValue.nextId + 1) threeRendered threeKind threeEquation
    (fresh.mono (Nat.le_trans oneSnapshot.le twoSnapshot.le)) distinct
  rw [← threeOfScalar] at threeSpec
  have threeSnapshot :=
    asnapshot_spec (fresh.mono (Nat.le_trans oneSnapshot.le twoSnapshot.le)) threeSpec
  refine athreeResult_spec (target := .word) fresh distinct oneSnapshot rfl twoSnapshot rfl
    threeSnapshot rfl ?_ ?_
  · intro name mem
    simp only [Expr.identifiers, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at mem
    rcases mem with same | (same | same) | same
    · refine Or.inr (Or.inr (Or.inr (same ▸ ?_)))
      cases op <;> simp [ternaryCallee, primitiveCallees, primitiveAliases]
    · exact Or.inl same
    · exact Or.inr (Or.inl same)
    · exact Or.inr (Or.inr (Or.inl same))
  · intro context environment store store₁ store₂ store₃ oneWord twoWord threeWord frames
      admitted oneEvaluates twoEvaluates threeEvaluates oneLookup twoLookup threeLookup
    have primitive : PrimitiveContext context := ready context admitted rfl
    obtain ⟨coreResult, sourceResult, coreApply, sourceApply, resultRepresents⟩ :=
      ternary_agree op context frames _ _ _ oneWord twoWord threeWord primitive oneLookup
        twoLookup threeLookup
    refine ⟨coreResult, sourceResult, ?_, sourceApply, resultRepresents⟩
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .ternary oneEvaluates twoEvaluates threeEvaluates coreApply

theorem aRenderIH_pair {left right : CoreExpr} (leftIH : ARenderIH left)
    (rightIH : ARenderIH right) : ARenderIH (.pair left right) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨leftKind, rightKind, resultPair⟩ := AggregateKinds.pair accepted
  have targetPair : target = .wordPair := by
    cases target <;> first | rfl | cases resultPair
  subst targetPair
  obtain ⟨leftRendered, leftValue, rightRendered, rightValue, leftEquation, leftNamed,
    rightEquation, rightNamed, rfl⟩ := AggregateEquations.pair_ok equation
  have leftSpec := leftIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .word bindings indent first leftRendered leftKind leftEquation fresh distinct
  have rightSpec := rightIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .word bindings indent leftRendered.nextId rightRendered rightKind rightEquation
    (fresh.mono leftSpec.le) distinct
  refine atwoResult_spec (target := .wordPair) fresh distinct leftSpec leftNamed rightSpec
    rightNamed (fun name mem => by
      simp only [Expr.identifiers, List.mem_append, List.mem_singleton] at mem
      rcases mem with same | same
      · exact Or.inl same
      · exact Or.inr (Or.inl same)) ?_
  intro context environment store store₁ store₂ leftWord rightWord frames _ leftEvaluates
    rightEvaluates leftLookup rightLookup
  refine ⟨.pair (.word leftWord) (.word rightWord), .pair leftWord.val rightWord.val, ?_, ?_,
    leftWord, rightWord, rfl, rfl⟩
  · simp only [Solcore.Core.Wire.Expr.toCore]
    exact .pair leftEvaluates rightEvaluates
  · simp [Expr.eval, leftLookup, rightLookup]

theorem aRenderIH_inLeft {type : Solcore.Core.Wire.Ty} {payload : CoreExpr}
    (payloadIH : ARenderIH payload) : ARenderIH (.inLeft type payload) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨rfl, payloadKind, resultSum⟩ := AggregateKinds.inLeft accepted
  have targetSum : target = .wordSum := by
    cases target <;> first | rfl | cases resultSum
  subst targetSum
  obtain ⟨payloadRendered, value, payloadEquation, named, rfl⟩ :=
    AggregateEquations.inLeft_ok equation
  have spec := payloadIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .word bindings indent first payloadRendered payloadKind payloadEquation fresh
    distinct
  refine aoneResult_spec (target := .wordSum) (by simp) fresh spec named
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
      exact Or.inl mem) ?_
  intro context environment store store₁ operandCore frames source _ _ _ evaluates lookup
    represents
  obtain ⟨word, rfl, rfl⟩ := represents
  refine ⟨.inLeft (Solcore.Core.Wire.Ty.toCore .word) (.word word), .inl word.val, store₁, ?_,
    Nat.le_refl _, fun _ _ => rfl, by simp [Expr.eval, lookup], Or.inl ⟨_, word, rfl, rfl⟩⟩
  simp only [Solcore.Core.Wire.Expr.toCore]
  exact .inLeft evaluates

theorem aRenderIH_inRight {type : Solcore.Core.Wire.Ty} {payload : CoreExpr}
    (payloadIH : ARenderIH payload) : ARenderIH (.inRight type payload) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨rfl, payloadKind, resultSum⟩ := AggregateKinds.inRight accepted
  have targetSum : target = .wordSum := by
    cases target <;> first | rfl | cases resultSum
  subst targetSum
  obtain ⟨payloadRendered, value, payloadEquation, named, rfl⟩ :=
    AggregateEquations.inRight_ok equation
  have spec := payloadIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .word bindings indent first payloadRendered payloadKind payloadEquation fresh
    distinct
  refine aoneResult_spec (target := .wordSum) (by simp) fresh spec named
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
      exact Or.inl mem) ?_
  intro context environment store store₁ operandCore frames source _ _ _ evaluates lookup
    represents
  obtain ⟨word, rfl, rfl⟩ := represents
  refine ⟨.inRight (Solcore.Core.Wire.Ty.toCore .word) (.word word), .inr word.val, store₁, ?_,
    Nat.le_refl _, fun _ _ => rfl, by simp [Expr.eval, lookup], Or.inr ⟨_, word, rfl, rfl⟩⟩
  simp only [Solcore.Core.Wire.Expr.toCore]
  exact .inRight evaluates

/-- A direct call to an earlier helper. The helper cannot reach the caller's
cells, so the call keeps every existing location of the store. -/
theorem aRenderIH_apply {index : Nat} {argument : CoreExpr} (argumentIH : ARenderIH argument) :
    ARenderIH (.apply (.var index) argument) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨_, _, argumentKind, resultWord⟩ := AggregateKinds.apply accepted
  have targetWord : target = .word := by
    cases target <;> first | rfl | cases resultWord
  subst targetWord
  obtain ⟨outside, callee, argumentRendered, value, found, argumentEquation, named, rfl⟩ :=
    AggregateEquations.apply_ok equation
  have spec := argumentIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .word bindings indent first argumentRendered argumentKind argumentEquation fresh
    distinct
  refine aoneResult_spec (target := .word) (by simp) fresh spec named
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with same | same
      · exact Or.inr (Or.inl (same ▸ List.mem_of_getElem? found))
      · exact Or.inl same) ?_
  intro context environment store store₁ operandCore frames source _ _ functionsOk evaluates
    lookup represents
  obtain ⟨word, rfl, rfl⟩ := represents
  obtain ⟨parameterType, resultType, body, captured, closureFound, behaves⟩ :=
    functionsOk (index - bindings.length) callee found
  obtain ⟨result, store₂, bodyEvaluates, grows, keepsStore, callResult⟩ := behaves word store₁
  have closureAt : environment[index]? =
      some (.closure parameterType resultType body captured) := by
    rw [List.getElem?_drop] at closureFound
    have position : bindings.length + (index - bindings.length) = index := by omega
    rwa [position] at closureFound
  refine ⟨.word result, .word result.val, store₂, ?_, grows, keepsStore, ?_, result, rfl, rfl⟩
  · simp only [Solcore.Core.Wire.Expr.toCore]
    exact .apply (.var closureAt) evaluates bodyEvaluates
  · simp [Expr.eval, lookup, callResult]

end

end Solcore.Synthesis.Source.ScalarMeaning

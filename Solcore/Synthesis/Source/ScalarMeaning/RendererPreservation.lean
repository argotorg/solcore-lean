import Solcore.Synthesis.Source.ScalarMeaning.Renderer

/-! Per-constructor simulation lemmas and the structural induction over the
actual scalar renderer, including direct calls to earlier helpers. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target acceptsAt functionAcceptsAt)
open Solcore.Synthesis.Source.ScalarRenderer (Rendered)

theorem classified_mono {locals : List String} {first last first' last' : Nat} {name : String}
    (classified : name ∈ locals ∨ AllocatedIn first last name) (low : first' ≤ first)
    (high : last ≤ last') : name ∈ locals ∨ AllocatedIn first' last' name := by
  rcases classified with mem | allocated
  · exact Or.inl mem
  · exact Or.inr (allocated_mono allocated low high)

theorem named_mono {locals functions : List String} {first last first' last' : Nat}
    {name : String} (named : name ∈ locals ∨ name ∈ functions ∨ AllocatedIn first last name)
    (low : first' ≤ first) (high : last ≤ last') :
    name ∈ locals ∨ name ∈ functions ∨ AllocatedIn first' last' name := by
  rcases named with mem | mem | allocated
  · exact Or.inl mem
  · exact Or.inr (Or.inl mem)
  · exact Or.inr (Or.inr (allocated_mono allocated low high))

theorem named_of_classified {locals functions : List String} {first last first' last' : Nat}
    {name : String} (classified : name ∈ locals ∨ AllocatedIn first last name)
    (low : first' ≤ first) (high : last ≤ last') :
    name ∈ locals ∨ name ∈ functions ∨ AllocatedIn first' last' name := by
  rcases classified with mem | allocated
  · exact Or.inl mem
  · exact Or.inr (Or.inr (allocated_mono allocated low high))

/-- One declaration of a fresh temporary initialized from a closed source
expression. -/
private theorem declare_simulates {expression : CoreExpr} {target : Target}
    {functions locals : List String} {first : Nat} {initializer : Expr} {core : CoreValue}
    {value : Value}
    (evaluates : ∀ (environment : Solcore.Core.Environment) (store : Solcore.Core.Store),
      Solcore.Core.Evaluates environment store expression.toCore core store)
    (represents : Represents target core value)
    (initialized : ∀ (context : Context) (frames : Frames),
      initializer.eval context frames = some value) :
    Simulates expression target functions locals first (first + 1)
      [.letDecl (temporary first) (LocalType.ofTarget target) initializer] (temporary first) := by
  intro context environment store scope outer _ _ _
  refine ⟨core, value, (temporary first, value) :: scope, outer, [temporary first],
    evaluates environment store, represents, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · simp [Stmt.execList, Stmt.exec, initialized, represents.admits, Frames.declare]
  · simp [Frames.lookup_declared]
  · intro name notAllocated
    have different : temporary first ≠ name := fun same =>
      notAllocated (same ▸ allocated_temporary (Nat.le_refl first) (Nat.lt_succ_self first))
    rw [Frames.lookup_declared, if_neg different]
  · intro name mem
    simp only [List.mem_singleton] at mem
    subst mem
    exact allocated_temporary (Nat.le_refl first) (Nat.lt_succ_self first)

theorem renderIH_word (value : Solcore.Core.Word) : RenderIH (.word value) := by
  intro functions depth prior target locals indent first rendered accepted equation _
  have targetWord : target = .word := by
    cases target
    · rfl
    · simp [functionAcceptsAt, target_beq_iff] at accepted
  subst targetWord
  rw [RendererEquations.word] at equation
  cases equation
  refine ⟨[.letDecl (temporary first) .word (.number value.val)], by simp [Stmt.listLines],
    Nat.le_succ first,
    Or.inr (allocated_temporary (Nat.le_refl first) (Nat.lt_succ_self first)), ?_, ?_⟩
  · intro name mem
    simp [Stmt.listIdentifiers, Stmt.identifiers, Expr.identifiers] at mem
    subst mem
    exact Or.inr (Or.inr (allocated_temporary (Nat.le_refl first) (Nat.lt_succ_self first)))
  · exact declare_simulates (target := .word)
      (fun _ _ => by simp only [Solcore.Core.Wire.Expr.toCore]; exact .word)
      ⟨value, rfl, rfl⟩ (fun _ _ => by simp [Expr.eval, word_lt_modulus])

theorem renderIH_bool (value : Bool) : RenderIH (.bool value) := by
  intro functions depth prior target locals indent first rendered accepted equation _
  have targetBool : target = .bool := by
    cases target
    · simp [functionAcceptsAt, target_beq_iff] at accepted
    · rfl
  subst targetBool
  rw [RendererEquations.bool] at equation
  cases equation
  refine ⟨[.letDecl (temporary first) .bool (.bool value)], by simp [Stmt.listLines],
    Nat.le_succ first,
    Or.inr (allocated_temporary (Nat.le_refl first) (Nat.lt_succ_self first)), ?_, ?_⟩
  · intro name mem
    simp [Stmt.listIdentifiers, Stmt.identifiers, Expr.identifiers] at mem
    subst mem
    exact Or.inr (Or.inr (allocated_temporary (Nat.le_refl first) (Nat.lt_succ_self first)))
  · exact declare_simulates (target := .bool)
      (fun _ _ => by simp only [Solcore.Core.Wire.Expr.toCore]; exact .bool)
      ⟨value, rfl, rfl⟩ (fun _ _ => rfl)

theorem renderIH_var (index : Nat) : RenderIH (.var index) := by
  intro functions depth prior target locals indent first rendered accepted equation _
  have targetWord : target = .word := by
    cases target
    · rfl
    · simp [functionAcceptsAt, target_beq_iff] at accepted
  subst targetWord
  rw [RendererEquations.var] at equation
  cases found : locals[index]? with
  | none => simp [found] at equation
  | some binding =>
      simp only [found, Except.ok.injEq] at equation
      subst equation
      refine ⟨[], rfl, Nat.le_refl first, Or.inl (List.mem_of_getElem? found),
        by simp [Stmt.listIdentifiers], ?_⟩
      intro context environment store scope outer agree _ _
      obtain ⟨word, inEnvironment, lookup⟩ := agree index binding found
      refine ⟨.word word, .word word.val, scope, outer, [], ?_, ⟨word, rfl, rfl⟩, rfl, lookup,
        fun _ _ => rfl, rfl, rfl, by simp⟩
      simp only [Solcore.Core.Wire.Expr.toCore]
      exact .var inEnvironment

theorem renderIH_letE {initializer body : CoreExpr} (initializerIH : RenderIH initializer)
    (bodyIH : RenderIH body) : RenderIH (.letE initializer body) := by
  intro functions depth prior target locals indent first rendered accepted equation fresh
  simp only [functionAcceptsAt, Bool.and_eq_true] at accepted
  obtain ⟨initializerAccepted, bodyAccepted⟩ := accepted
  rw [RendererEquations.letE] at equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rest, restEquation, equation⟩ := except_bind_eq_ok equation
  cases equation
  unfold RenderSpec
  dsimp only
  obtain ⟨initializerStatements, initializerLines, initializerLe, initializerValue,
    initializerNames, initializerSimulates⟩ :=
    initializerIH functions depth prior .word locals indent first value initializerAccepted
      valueEquation fresh
  have bodyFresh : ∀ name ∈ temporary value.nextId :: locals,
      OlderThan (value.nextId + 1) name := by
    intro name mem
    rcases List.mem_cons.mp mem with same | mem
    · subst same
      exact temporary_older value.nextId
    · exact older_mono (fresh name mem) (by omega)
  obtain ⟨bodyStatements, bodyLines, bodyLe, bodyValue, bodyNames, bodySimulates⟩ :=
    bodyIH functions (depth + 1) prior target (temporary value.nextId :: locals) indent
      (value.nextId + 1) rest bodyAccepted restEquation bodyFresh
  refine ⟨initializerStatements ++ [.letDecl (temporary value.nextId) .word (.name value.value)] ++
      bodyStatements, ?_, by omega, ?_, ?_, ?_⟩
  · simp only [Stmt.listLines_append, initializerLines, bodyLines, Stmt.listLines,
      List.append_nil]
  · rcases bodyValue with mem | allocated
    · rcases List.mem_cons.mp mem with same | mem
      · exact Or.inr ⟨value.nextId, same, initializerLe, by omega⟩
      · exact Or.inl mem
    · exact Or.inr (allocated_mono allocated (by omega) (Nat.le_refl _))
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at mem
    rcases mem with (mem | same | same) | mem
    · exact named_mono (initializerNames name mem) (Nat.le_refl _) (by omega)
    · exact Or.inr (Or.inr ⟨value.nextId, same, initializerLe, by omega⟩)
    · subst same
      exact named_of_classified initializerValue (Nat.le_refl _) (by omega)
    · rcases bodyNames name mem with mem | mem | allocated
      · rcases List.mem_cons.mp mem with same | mem
        · exact Or.inr (Or.inr ⟨value.nextId, same, initializerLe, by omega⟩)
        · exact Or.inl mem
      · exact Or.inr (Or.inl mem)
      · exact Or.inr (Or.inr (allocated_mono allocated (by omega) (Nat.le_refl _)))
  · intro context environment store scope outer agree lengthOk functionsOk
    obtain ⟨initializerCore, initializerSource, scope₁, outer₁, added₁, initializerEvaluates,
      initializerRepresents, initializerExec, initializerLookup, initializerKeeps,
      initializerShape, initializerScope, initializerAdded⟩ :=
      initializerSimulates context environment store scope outer agree lengthOk functionsOk
    obtain ⟨word, rfl, rfl⟩ := initializerRepresents
    have keepsLocals : ∀ name ∈ locals,
        Frames.lookup (scope₁ :: outer₁) name = Frames.lookup (scope :: outer) name :=
      fun name mem => initializerKeeps name
        (not_allocated_of_older (fresh name mem) (Nat.le_refl first))
    have bodyAgree : LocalsAgree
        (((temporary value.nextId, .word word.val) :: scope₁) :: outer₁)
        (temporary value.nextId :: locals) (.word word :: environment) := by
      intro index name found
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst found
          exact ⟨word, rfl, by simp [Frames.lookup_declared]⟩
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          obtain ⟨other, inEnvironment, lookup⟩ := agree index name found
          have mem := List.mem_of_getElem? found
          have different : temporary value.nextId ≠ name := by
            intro same
            have := fresh name mem value.nextId same.symm
            omega
          refine ⟨other, by simpa using inEnvironment, ?_⟩
          rw [Frames.lookup_declared, if_neg different, keepsLocals name mem]
          exact lookup
    obtain ⟨bodyCore, bodySource, scope₂, outer₂, added₂, bodyEvaluates, bodyRepresents,
      bodyExec, bodyLookup, bodyKeeps, bodyShape, bodyScope, bodyAdded⟩ :=
      bodySimulates context (.word word :: environment) store
        ((temporary value.nextId, .word word.val) :: scope₁) outer₁ bodyAgree
        (by simpa using lengthOk) (by simpa using functionsOk)
    refine ⟨bodyCore, bodySource, scope₂, outer₂, added₂ ++ temporary value.nextId :: added₁,
      ?_, bodyRepresents, ?_, bodyLookup, ?_, bodyShape.trans initializerShape, ?_, ?_⟩
    · simp only [Solcore.Core.Wire.Expr.toCore]
      exact .letE initializerEvaluates bodyEvaluates
    · rw [Stmt.execList_append, Stmt.execList_append, initializerExec]
      simp [Stmt.execList, Stmt.exec, Expr.eval, initializerLookup, LocalType.admits,
        Frames.declare, bodyExec]
    · intro name notAllocated
      have notBody : ¬ AllocatedIn (value.nextId + 1) rest.nextId name := fun allocated =>
        notAllocated (allocated_mono allocated (by omega) (Nat.le_refl _))
      have notInitializer : ¬ AllocatedIn first value.nextId name := fun allocated =>
        notAllocated (allocated_mono allocated (Nat.le_refl _) (by omega))
      have different : temporary value.nextId ≠ name := fun same =>
        notAllocated (same ▸ allocated_temporary initializerLe (by omega))
      rw [bodyKeeps name notBody, Frames.lookup_declared, if_neg different,
        initializerKeeps name notInitializer]
    · rw [bodyScope, show Scope.names ((temporary value.nextId, .word word.val) :: scope₁) =
        temporary value.nextId :: scope₁.names from rfl, initializerScope]
      simp
    · intro name mem
      simp only [List.mem_append, List.mem_cons] at mem
      rcases mem with mem | same | mem
      · exact allocated_mono (bodyAdded name mem) (by omega) (Nat.le_refl _)
      · exact ⟨value.nextId, same, initializerLe, by omega⟩
      · exact allocated_mono (initializerAdded name mem) (Nat.le_refl _) (by omega)

/-- After a fresh temporary receives a result, every name outside the
allocated range keeps its earlier binding. -/
private theorem result_keeps {first index : Nat} {scope₁ : Scope} {outer₁ : Frames}
    {scope : Scope} {outer : Frames} {result : Value} (fresh : first ≤ index)
    (keeps : ∀ name, ¬ AllocatedIn first index name →
      Frames.lookup (scope₁ :: outer₁) name = Frames.lookup (scope :: outer) name) :
    ∀ name, ¬ AllocatedIn first (index + 1) name →
      Frames.lookup (((temporary index, result) :: scope₁) :: outer₁) name =
        Frames.lookup (scope :: outer) name := by
  intro name notAllocated
  have notEarlier : ¬ AllocatedIn first index name := fun allocated =>
    notAllocated (allocated_mono allocated (Nat.le_refl _) (by omega))
  have different : temporary index ≠ name := fun same =>
    notAllocated (same ▸ allocated_temporary fresh (Nat.lt_succ_self _))
  rw [Frames.lookup_declared, if_neg different, keeps name notEarlier]

theorem renderIH_unary {op : Solcore.Core.Wire.UnaryOp} {operand : CoreExpr}
    (operandIH : RenderIH operand) : RenderIH (.unary op operand) := by
  intro functions depth prior target locals indent first rendered accepted equation fresh
  rw [RendererEquations.unary] at equation
  cases selected : sourceUnary? op with
  | none => simp [selected] at equation
  | some sourceOp =>
    simp only [selected] at equation
    obtain ⟨targetEq, operandAccepted⟩ := acceptsAt_unary selected accepted
    obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
    cases equation
    unfold RenderSpec
    dsimp only
    obtain ⟨operandStatements, operandLines, operandLe, operandValue, operandNames,
      operandSimulates⟩ :=
      operandIH functions depth prior _ locals indent first value operandAccepted valueEquation
        fresh
    refine ⟨operandStatements ++ [.letDecl (temporary value.nextId) (LocalType.ofTarget target)
        (.unary sourceOp (.name value.value))], ?_, by omega,
      Or.inr (allocated_temporary operandLe (Nat.lt_succ_self _)), ?_, ?_⟩
    · simp only [Stmt.listLines_append, operandLines, Stmt.listLines, List.append_nil]
    · intro name mem
      simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
        Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false] at mem
      rcases mem with mem | same | same
      · exact named_mono (operandNames name mem) (Nat.le_refl _) (by omega)
      · exact Or.inr (Or.inr ⟨value.nextId, same, operandLe, by omega⟩)
      · subst same
        exact named_of_classified operandValue (Nat.le_refl _) (by omega)
    · intro context environment store scope outer agree lengthOk functionsOk
      obtain ⟨operandCore, operandSource, scope₁, outer₁, added₁, operandEvaluates,
        operandRepresents, operandExec, operandLookup, operandKeeps, operandShape,
        operandScope, operandAdded⟩ :=
        operandSimulates context environment store scope outer agree lengthOk functionsOk
      obtain ⟨coreResult, sourceResult, coreApply, sourceApply, resultRepresents⟩ :=
        unary_agree selected operandRepresents
      rw [← targetEq] at resultRepresents
      refine ⟨coreResult, sourceResult, (temporary value.nextId, sourceResult) :: scope₁, outer₁,
        temporary value.nextId :: added₁, ?_, resultRepresents, ?_, ?_,
        result_keeps operandLe operandKeeps, operandShape, ?_, ?_⟩
      · simp only [Solcore.Core.Wire.Expr.toCore]
        exact .unary operandEvaluates coreApply
      · rw [Stmt.execList_append, operandExec]
        simp [Stmt.execList, Stmt.exec, Expr.eval, operandLookup, sourceApply,
          resultRepresents.admits, Frames.declare]
      · simp [Frames.lookup_declared]
      · rw [show Scope.names ((temporary value.nextId, sourceResult) :: scope₁) =
          temporary value.nextId :: scope₁.names from rfl, operandScope]
        simp
      · intro name mem
        rcases List.mem_cons.mp mem with same | mem
        · exact ⟨value.nextId, same, operandLe, Nat.lt_succ_self _⟩
        · exact allocated_mono (operandAdded name mem) (Nat.le_refl _) (by omega)

theorem renderIH_binary {op : Solcore.Core.Wire.BinaryOp} {left right : CoreExpr}
    (leftIH : RenderIH left) (rightIH : RenderIH right) : RenderIH (.binary op left right) := by
  intro functions depth prior target locals indent first rendered accepted equation fresh
  rw [RendererEquations.binary] at equation
  cases selected : sourceBinary? op with
  | none => simp [selected] at equation
  | some sourceOp =>
    simp only [selected] at equation
    obtain ⟨targetEq, leftAccepted, rightAccepted⟩ := acceptsAt_binary selected accepted
    obtain ⟨leftValue, leftEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨rightValue, rightEquation, equation⟩ := except_bind_eq_ok equation
    cases equation
    unfold RenderSpec
    dsimp only
    obtain ⟨leftStatements, leftLines, leftLe, leftValueName, leftNames, leftSimulates⟩ :=
      leftIH functions depth prior .word locals indent first leftValue leftAccepted leftEquation
        fresh
    have rightFresh : ∀ name ∈ locals, OlderThan leftValue.nextId name :=
      fun name mem => older_mono (fresh name mem) leftLe
    obtain ⟨rightStatements, rightLines, rightLe, rightValueName, rightNames, rightSimulates⟩ :=
      rightIH functions depth prior .word locals indent leftValue.nextId rightValue rightAccepted
        rightEquation rightFresh
    refine ⟨leftStatements ++ rightStatements ++ [.letDecl (temporary rightValue.nextId)
        (LocalType.ofTarget target)
        (.binary sourceOp (.name leftValue.value) (.name rightValue.value))], ?_, by omega,
      Or.inr (allocated_temporary (by omega) (Nat.lt_succ_self _)), ?_, ?_⟩
    · simp only [Stmt.listLines_append, leftLines, rightLines, Stmt.listLines, List.append_nil]
    · intro name mem
      simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
        Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false] at mem
      rcases mem with (mem | mem) | same | same | same
      · exact named_mono (leftNames name mem) (Nat.le_refl _) (by omega)
      · exact named_mono (rightNames name mem) leftLe (by omega)
      · exact Or.inr (Or.inr ⟨rightValue.nextId, same, by omega, by omega⟩)
      · subst same
        exact named_of_classified leftValueName (Nat.le_refl _) (by omega)
      · subst same
        exact named_of_classified rightValueName leftLe (by omega)
    · intro context environment store scope outer agree lengthOk functionsOk
      obtain ⟨leftCore, leftSource, scope₁, outer₁, added₁, leftEvaluates, leftRepresents,
        leftExec, leftLookup, leftKeeps, leftShape, leftScope, leftAdded⟩ :=
        leftSimulates context environment store scope outer agree lengthOk functionsOk
      have rightAgree : LocalsAgree (scope₁ :: outer₁) locals environment :=
        agree.transfer fun name mem =>
          leftKeeps name (not_allocated_of_older (fresh name mem) (Nat.le_refl first))
      obtain ⟨rightCore, rightSource, scope₂, outer₂, added₂, rightEvaluates, rightRepresents,
        rightExec, rightLookup, rightKeeps, rightShape, rightScope, rightAdded⟩ :=
        rightSimulates context environment store scope₁ outer₁ rightAgree lengthOk functionsOk
      obtain ⟨leftWord, rfl, rfl⟩ := leftRepresents
      obtain ⟨rightWord, rfl, rfl⟩ := rightRepresents
      obtain ⟨coreResult, sourceResult, coreApply, sourceApply, resultRepresents⟩ :=
        binary_agree selected leftWord rightWord
      rw [← targetEq] at resultRepresents
      have leftSurvives :
          Frames.lookup (scope₂ :: outer₂) leftValue.value = some (.word leftWord.val) := by
        rw [rightKeeps _ (value_not_reallocated fresh leftLe leftValueName)]
        exact leftLookup
      have keeps : ∀ name, ¬ AllocatedIn first rightValue.nextId name →
          Frames.lookup (scope₂ :: outer₂) name = Frames.lookup (scope :: outer) name := by
        intro name notAllocated
        rw [rightKeeps name fun allocated =>
            notAllocated (allocated_mono allocated leftLe (Nat.le_refl _)),
          leftKeeps name fun allocated =>
            notAllocated (allocated_mono allocated (Nat.le_refl _) rightLe)]
      refine ⟨coreResult, sourceResult, (temporary rightValue.nextId, sourceResult) :: scope₂,
        outer₂, temporary rightValue.nextId :: (added₂ ++ added₁), ?_, resultRepresents, ?_, ?_,
        result_keeps (by omega) keeps, rightShape.trans leftShape, ?_, ?_⟩
      · simp only [Solcore.Core.Wire.Expr.toCore]
        exact .binary leftEvaluates rightEvaluates coreApply
      · rw [Stmt.execList_append, Stmt.execList_append, leftExec]
        simp [Stmt.execList, Stmt.exec, Expr.eval, rightExec, leftSurvives, rightLookup,
          sourceApply, resultRepresents.admits, Frames.declare]
      · simp [Frames.lookup_declared]
      · rw [show Scope.names ((temporary rightValue.nextId, sourceResult) :: scope₂) =
          temporary rightValue.nextId :: scope₂.names from rfl, rightScope, leftScope]
        simp
      · intro name mem
        simp only [List.mem_cons, List.mem_append] at mem
        rcases mem with same | mem | mem
        · exact ⟨rightValue.nextId, same, by omega, Nat.lt_succ_self _⟩
        · exact allocated_mono (rightAdded name mem) leftLe (by omega)
        · exact allocated_mono (leftAdded name mem) (Nat.le_refl _) (by omega)

/-- A direct call to an earlier helper: the argument value is passed to the
helper's denotation in the call context, as Core applies its closure. -/
theorem renderIH_apply {index : Nat} {argument : CoreExpr} (argumentIH : RenderIH argument) :
    RenderIH (.apply (.var index) argument) := by
  intro functions depth prior target locals indent first rendered accepted equation fresh
  simp only [functionAcceptsAt, Bool.and_eq_true, target_beq_iff] at accepted
  obtain ⟨⟨targetWord, _⟩, argumentAccepted⟩ := accepted
  subst targetWord
  rw [RendererEquations.apply] at equation
  by_cases rejected : (functions.isEmpty || decide (index < locals.length)) = true
  · rw [if_pos rejected] at equation
    cases equation
  rw [if_neg rejected] at equation
  have outside : locals.length ≤ index := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at rejected
    omega
  cases found : functions[index - locals.length]? with
  | none => simp [found] at equation
  | some callee =>
    simp only [found] at equation
    obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
    cases equation
    unfold RenderSpec
    dsimp only
    obtain ⟨argumentStatements, argumentLines, argumentLe, argumentValue, argumentNames,
      argumentSimulates⟩ :=
      argumentIH functions depth prior .word locals indent first value argumentAccepted
        valueEquation fresh
    refine ⟨argumentStatements ++ [.letDecl (temporary value.nextId) .word
        (.call1 callee (.name value.value))], ?_, by omega,
      Or.inr (allocated_temporary argumentLe (Nat.lt_succ_self _)), ?_, ?_⟩
    · simp only [Stmt.listLines_append, argumentLines, Stmt.listLines, List.append_nil]
    · intro name mem
      simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
        Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false] at mem
      rcases mem with mem | same | same | same
      · exact named_mono (argumentNames name mem) (Nat.le_refl _) (by omega)
      · exact Or.inr (Or.inr ⟨value.nextId, same, argumentLe, by omega⟩)
      · subst same
        exact Or.inr (Or.inl (List.mem_of_getElem? found))
      · subst same
        exact named_of_classified argumentValue (Nat.le_refl _) (by omega)
    · intro context environment store scope outer agree lengthOk functionsOk
      obtain ⟨argumentCore, argumentSource, scope₁, outer₁, added₁, argumentEvaluates,
        argumentRepresents, argumentExec, argumentLookup, argumentKeeps, argumentShape,
        argumentScope, argumentAdded⟩ :=
        argumentSimulates context environment store scope outer agree lengthOk functionsOk
      obtain ⟨word, rfl, rfl⟩ := argumentRepresents
      obtain ⟨parameterType, resultType, body, captured, closureFound, behaves⟩ :=
        functionsOk (index - locals.length) callee found
      obtain ⟨result, bodyEvaluates, called⟩ := behaves word store
      have closureAt : environment[index]? =
          some (.closure parameterType resultType body captured) := by
        rw [List.getElem?_drop] at closureFound
        have position : locals.length + (index - locals.length) = index := by omega
        rwa [position] at closureFound
      refine ⟨.word result, .word result.val, (temporary value.nextId, .word result.val) :: scope₁,
        outer₁, temporary value.nextId :: added₁, ?_, ⟨result, rfl, rfl⟩, ?_, ?_,
        result_keeps argumentLe argumentKeeps, argumentShape, ?_, ?_⟩
      · simp only [Solcore.Core.Wire.Expr.toCore]
        exact .apply (.var closureAt) argumentEvaluates bodyEvaluates
      · rw [Stmt.execList_append, argumentExec]
        simp [Stmt.execList, Stmt.exec, Expr.eval, argumentLookup, called, LocalType.admits,
          Frames.declare]
      · simp [Frames.lookup_declared]
      · rw [show Scope.names ((temporary value.nextId, .word result.val) :: scope₁) =
          temporary value.nextId :: scope₁.names from rfl, argumentScope]
        simp
      · intro name mem
        rcases List.mem_cons.mp mem with same | mem
        · exact ⟨value.nextId, same, argumentLe, Nat.lt_succ_self _⟩
        · exact allocated_mono (argumentAdded name mem) (Nat.le_refl _) (by omega)

/-- A branch block runs in a fresh scope and ends by assigning its value to
the `if` result, which was declared before the `if`. After the block's scope
is discarded, only the result binding has changed. -/
private theorem branch_simulates {expression : CoreExpr} {target : Target}
    {functions locals : List String} {low high : Nat} {statements : List Stmt}
    {valueName result : String}
    (simulates : Simulates expression target functions locals low high statements valueName)
    (resultOutside : ¬ AllocatedIn low high result) {context : Context}
    {environment : Solcore.Core.Environment} {store : Solcore.Core.Store}
    {scope : Scope} {outer : Frames}
    (agree : LocalsAgree ([] :: scope :: outer) locals environment)
    (lengthOk : locals.length ≤ environment.length)
    (functionsOk : FunctionsAgree context functions (environment.drop locals.length))
    (declared : Frames.lookup (scope :: outer) result = some (zeroValue target)) :
    ∃ (coreValue : CoreValue) (value : Value) (top scope' : Scope) (outer' : Frames),
      Solcore.Core.Evaluates environment store expression.toCore coreValue store ∧
      Represents target coreValue value ∧
      Stmt.execList context ([] :: scope :: outer)
          (statements ++ [.assign result (.name valueName)]) =
        some (top :: scope' :: outer') ∧
      scope'.names = scope.names ∧ outer'.shape = outer.shape ∧
      ∀ name, ¬ AllocatedIn low high name →
        Frames.lookup (scope' :: outer') name =
          if result = name then some value else Frames.lookup (scope :: outer) name := by
  obtain ⟨coreValue, value, top₁, frames₁, added, evaluates, represents, exec, lookup, keeps,
    shape, topNames, addedAllocated⟩ :=
    simulates context environment store [] (scope :: outer) agree lengthOk functionsOk
  have resultFound : Frames.lookup (top₁ :: frames₁) result = some (zeroValue target) := by
    rw [keeps result resultOutside]
    exact declared
  obtain ⟨frames₂, assigned, shape₂, lookup₂⟩ :=
    Frames.assign_spec (frames := top₁ :: frames₁) value resultFound
  have shapeCons : frames₂.shape = top₁.names :: scope.names :: outer.shape := by
    rw [shape₂]
    simp only [Frames.shape, List.map_cons] at shape ⊢
    rw [shape]
  obtain ⟨top₂, scope', outer', rfl⟩ :
      ∃ top₂ scope' outer', frames₂ = top₂ :: scope' :: outer' := by
    match frames₂, shapeCons with
    | top₂ :: scope' :: outer', _ => exact ⟨top₂, scope', outer', rfl⟩
    | [], impossible => simp [Frames.shape] at impossible
    | [_], impossible => simp [Frames.shape] at impossible
  simp only [Frames.shape, List.map_cons, List.cons.injEq] at shapeCons
  obtain ⟨topNames₂, scopeNames, outerShape⟩ := shapeCons
  refine ⟨coreValue, value, top₂, scope', outer', evaluates, represents, ?_, scopeNames,
    outerShape, ?_⟩
  · rw [Stmt.execList_append, exec]
    simp [Stmt.execList, Stmt.exec, Expr.eval, lookup, resultFound,
      represents.sameType_zero, assigned]
  · intro name notAllocated
    have absent : name ∉ top₂.names := by
      rw [topNames₂, topNames]
      intro mem
      simp only [Scope.names, List.map_nil, List.append_nil] at mem
      exact notAllocated (addedAllocated name mem)
    rw [← Frames.lookup_cons_of_not_mem (scope' :: outer') absent, lookup₂ name,
      keeps name notAllocated, Frames.lookup_nil_cons]

theorem zeroExpr_identifiers (target : Target) : (zeroExpr target).identifiers = [] := by
  cases target <;> rfl

theorem renderIH_ifE {condition yes no : CoreExpr} (conditionIH : RenderIH condition)
    (yesIH : RenderIH yes) (noIH : RenderIH no) : RenderIH (.ifE condition yes no) := by
  intro functions depth prior target locals indent first rendered accepted equation fresh
  simp only [functionAcceptsAt, Bool.and_eq_true] at accepted
  obtain ⟨⟨conditionAccepted, yesAccepted⟩, noAccepted⟩ := accepted
  rw [RendererEquations.ifE] at equation
  obtain ⟨tested, testedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨selected, selectedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨fallback, fallbackEquation, equation⟩ := except_bind_eq_ok equation
  cases equation
  unfold RenderSpec
  dsimp only
  obtain ⟨conditionStatements, conditionLines, conditionLe, conditionValue, conditionNames,
    conditionSimulates⟩ :=
    conditionIH functions depth prior .bool locals indent first tested conditionAccepted
      testedEquation fresh
  obtain ⟨yesStatements, yesLines, yesLe, yesValue, yesNames, yesSimulates⟩ :=
    yesIH functions depth prior target locals (indent + 4) (tested.nextId + 1) selected
      yesAccepted selectedEquation (fun name mem => older_mono (fresh name mem) (by omega))
  obtain ⟨noStatements, noLines, noLe, noValue, noNames, noSimulates⟩ :=
    noIH functions depth prior target locals (indent + 4) selected.nextId fallback noAccepted
      fallbackEquation (fun name mem => older_mono (fresh name mem) (by omega))
  refine ⟨conditionStatements ++
      [.letDecl (temporary tested.nextId) (LocalType.ofTarget target) (zeroExpr target),
        .ifElse (.name tested.value)
          (yesStatements ++ [.assign (temporary tested.nextId) (.name selected.value)])
          (noStatements ++ [.assign (temporary tested.nextId) (.name fallback.value)])],
    ?_, by omega, Or.inr (allocated_temporary conditionLe (by omega)), ?_, ?_⟩
  · simp only [Stmt.listLines_append, conditionLines, yesLines, noLines, Stmt.listLines,
      Stmt.lines, Expr.print, zeroExpr_print, List.append_nil, List.append_assoc,
      List.cons_append, List.nil_append]
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, Expr.identifiers, zeroExpr_identifiers, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with mem | same | (same | mem | same | same) | (mem | same | same)
    · exact named_mono (conditionNames name mem) (Nat.le_refl _) (by omega)
    · exact Or.inr (Or.inr ⟨tested.nextId, same, conditionLe, by omega⟩)
    · subst same
      exact named_of_classified conditionValue (Nat.le_refl _) (by omega)
    · exact named_mono (yesNames name mem) (by omega) (by omega)
    · exact Or.inr (Or.inr ⟨tested.nextId, same, conditionLe, by omega⟩)
    · subst same
      exact named_of_classified yesValue (by omega) (by omega)
    · exact named_mono (noNames name mem) (by omega) (Nat.le_refl _)
    · exact Or.inr (Or.inr ⟨tested.nextId, same, conditionLe, by omega⟩)
    · subst same
      exact named_of_classified noValue (by omega) (Nat.le_refl _)
  · intro context environment store scope outer agree lengthOk functionsOk
    obtain ⟨conditionCore, conditionSource, scope₁, outer₁, added₁, conditionEvaluates,
      conditionRepresents, conditionExec, conditionLookup, conditionKeeps, conditionShape,
      conditionScope, conditionAdded⟩ :=
      conditionSimulates context environment store scope outer agree lengthOk functionsOk
    obtain ⟨flag, rfl, rfl⟩ := conditionRepresents
    have resultOlder : ∀ name ∈ locals, temporary tested.nextId ≠ name := by
      intro name mem same
      have := fresh name mem tested.nextId same.symm
      omega
    have branchAgree : LocalsAgree
        ([] :: ((temporary tested.nextId, zeroValue target) :: scope₁) :: outer₁)
        locals environment := by
      refine agree.transfer fun name mem => ?_
      rw [Frames.lookup_nil_cons, Frames.lookup_declared, if_neg (resultOlder name mem),
        conditionKeeps name (not_allocated_of_older (fresh name mem) (Nat.le_refl _))]
    have declared : Frames.lookup (((temporary tested.nextId, zeroValue target) :: scope₁) ::
        outer₁) (temporary tested.nextId) = some (zeroValue target) := by
      simp [Frames.lookup_declared]
    have testedSurvives : Frames.lookup (((temporary tested.nextId, zeroValue target) :: scope₁) ::
        outer₁) tested.value = some (.bool flag) := by
      have different : temporary tested.nextId ≠ tested.value := by
        intro same
        rcases conditionValue with mem | allocated
        · exact resultOlder _ mem same
        · exact temporary_not_allocated (Or.inr (Nat.le_refl _)) (same ▸ allocated)
      rw [Frames.lookup_declared, if_neg different]
      exact conditionLookup
    have prefixExec : Stmt.execList context (scope :: outer) (conditionStatements ++
        [.letDecl (temporary tested.nextId) (LocalType.ofTarget target) (zeroExpr target)]) =
        some (((temporary tested.nextId, zeroValue target) :: scope₁) :: outer₁) := by
      rw [Stmt.execList_append, conditionExec]
      simp [Stmt.execList, Stmt.exec, zeroExpr_eval, zeroValue_admits, Frames.declare]
    have keepsOutside : ∀ name, ¬ AllocatedIn first fallback.nextId name →
        Frames.lookup (((temporary tested.nextId, zeroValue target) :: scope₁) :: outer₁) name =
          Frames.lookup (scope :: outer) name := by
      intro name notAllocated
      have different : temporary tested.nextId ≠ name := fun same =>
        notAllocated (same ▸ allocated_temporary conditionLe (by omega))
      rw [Frames.lookup_declared, if_neg different, conditionKeeps name fun allocated =>
        notAllocated (allocated_mono allocated (Nat.le_refl _) (by omega))]
    have resultScope : Scope.names ((temporary tested.nextId, zeroValue target) :: scope₁) =
        (temporary tested.nextId :: added₁) ++ scope.names := by
      rw [show Scope.names ((temporary tested.nextId, zeroValue target) :: scope₁) =
        temporary tested.nextId :: scope₁.names from rfl, conditionScope]
      simp
    have resultAdded : ∀ name ∈ temporary tested.nextId :: added₁,
        AllocatedIn first fallback.nextId name := by
      intro name mem
      rcases List.mem_cons.mp mem with same | mem
      · exact ⟨tested.nextId, same, conditionLe, by omega⟩
      · exact allocated_mono (conditionAdded name mem) (Nat.le_refl _) (by omega)
    cases flag with
    | true =>
        obtain ⟨branchCore, branchValue, top, scope', outer', branchEvaluates, branchRepresents,
          branchExec, scopeNames, outerShape, branchLookup⟩ :=
          branch_simulates yesSimulates (temporary_not_allocated (Or.inl (Nat.lt_succ_self _)))
            branchAgree lengthOk functionsOk declared
        refine ⟨branchCore, branchValue, scope', outer', temporary tested.nextId :: added₁,
          ?_, branchRepresents, ?_, ?_, ?_, outerShape.trans conditionShape,
          scopeNames.trans resultScope, resultAdded⟩
        · simp only [Solcore.Core.Wire.Expr.toCore]
          exact .ifTrue conditionEvaluates branchEvaluates
        · rw [List.append_cons, Stmt.execList_append, prefixExec]
          simp [Stmt.execList, Stmt.exec, Expr.eval, testedSurvives, branchExec]
        · rw [branchLookup _ (temporary_not_allocated (Or.inl (Nat.lt_succ_self _)))]
          simp
        · intro name notAllocated
          have notBranch : ¬ AllocatedIn (tested.nextId + 1) selected.nextId name :=
            fun allocated => notAllocated (allocated_mono allocated (by omega) (by omega))
          have different : temporary tested.nextId ≠ name := fun same =>
            notAllocated (same ▸ allocated_temporary conditionLe (by omega))
          rw [branchLookup name notBranch, if_neg different, keepsOutside name notAllocated]
    | false =>
        obtain ⟨branchCore, branchValue, top, scope', outer', branchEvaluates, branchRepresents,
          branchExec, scopeNames, outerShape, branchLookup⟩ :=
          branch_simulates noSimulates (temporary_not_allocated (Or.inl (by omega)))
            branchAgree lengthOk functionsOk declared
        refine ⟨branchCore, branchValue, scope', outer', temporary tested.nextId :: added₁,
          ?_, branchRepresents, ?_, ?_, ?_, outerShape.trans conditionShape,
          scopeNames.trans resultScope, resultAdded⟩
        · simp only [Solcore.Core.Wire.Expr.toCore]
          exact .ifFalse conditionEvaluates branchEvaluates
        · rw [List.append_cons, Stmt.execList_append, prefixExec]
          simp [Stmt.execList, Stmt.exec, Expr.eval, testedSurvives, branchExec]
        · rw [branchLookup _ (temporary_not_allocated (Or.inl (by omega)))]
          simp
        · intro name notAllocated
          have notBranch : ¬ AllocatedIn selected.nextId fallback.nextId name :=
            fun allocated => notAllocated (allocated_mono allocated (by omega) (Nat.le_refl _))
          have different : temporary tested.nextId ≠ name := fun same =>
            notAllocated (same ▸ allocated_temporary conditionLe (by omega))
          rw [branchLookup name notBranch, if_neg different, keepsOutside name notAllocated]

theorem renderIH_rejected (expression : CoreExpr)
    (rejected : ∀ (depth prior : Nat) (target : Target),
      functionAcceptsAt depth prior target expression = false) :
    RenderIH expression := by
  intro _ depth prior target _ _ _ _ accepted
  rw [rejected depth prior target] at accepted
  cases accepted

/-- The renderer rejects ternary operations, which the fragment admits. -/
theorem renderIH_ternary (op : Solcore.Core.Wire.TernaryOp) (first second third : CoreExpr) :
    RenderIH (.ternary op first second third) := by
  intro functions depth prior target locals indent next rendered _ equation
  simp [ScalarRenderer.renderWithFunctions] at equation

/-- Every admitted expression that the actual renderer accepts satisfies its
rendering specification, with or without earlier helpers. -/
theorem render_spec : (expression : CoreExpr) → RenderIH expression
  | .word value => renderIH_word value
  | .bool value => renderIH_bool value
  | .var index => renderIH_var index
  | .letE initializer body => renderIH_letE (render_spec initializer) (render_spec body)
  | .ifE condition yes no =>
      renderIH_ifE (render_spec condition) (render_spec yes) (render_spec no)
  | .unary _ operand => renderIH_unary (render_spec operand)
  | .binary _ left right => renderIH_binary (render_spec left) (render_spec right)
  | .ternary op first second third => renderIH_ternary op first second third
  | .apply (.var _) argument => renderIH_apply (render_spec argument)
  | .apply (.word _) _ | .apply (.bool _) _ | .apply .unit _ | .apply (.integer _) _
  | .apply (.pair _ _) _ | .apply (.first _) _ | .apply (.second _) _
  | .apply (.lambda _ _ _) _ | .apply (.apply _ _) _ | .apply (.inLeft _ _) _
  | .apply (.inRight _ _) _ | .apply (.caseE _ _ _) _ | .apply (.newCell _ _) _
  | .apply (.loadCell _) _ | .apply (.storeCell _ _) _ | .apply (.construct _ _) _
  | .apply (.matchData _ _ _ _) _ | .apply (.unary _ _) _ | .apply (.binary _ _ _) _
  | .apply (.ternary _ _ _ _) _ | .apply (.letE _ _) _ | .apply (.ifE _ _ _) _ =>
      renderIH_rejected _ fun _ _ _ => rfl
  | .unit => renderIH_rejected _ fun _ _ _ => rfl
  | .integer _ => renderIH_rejected _ fun _ _ _ => rfl
  | .pair _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .first _ => renderIH_rejected _ fun _ _ _ => rfl
  | .second _ => renderIH_rejected _ fun _ _ _ => rfl
  | .lambda _ _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .inLeft _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .inRight _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .caseE _ _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .newCell _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .loadCell _ => renderIH_rejected _ fun _ _ _ => rfl
  | .storeCell _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .construct _ _ => renderIH_rejected _ fun _ _ _ => rfl
  | .matchData _ _ _ _ => renderIH_rejected _ fun _ _ _ => rfl

end Solcore.Synthesis.Source.ScalarMeaning

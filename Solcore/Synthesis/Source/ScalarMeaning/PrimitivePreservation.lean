import Solcore.Synthesis.Source.ScalarMeaning.RendererPreservation
import Solcore.Synthesis.Source.ScalarMeaning.PrimitiveEquations
import Solcore.Synthesis.Source.ScalarMeaning.PrimitiveAgreement

/-! Simulation lemmas for raw `std.opcodes` calls, generic over a renderer
that copies each opcode operand into a fresh `word` temporary first, and their
instance for the actual `PrimitiveRenderer.render`. The call context must
resolve every primitive alias to its opcode and `tobool` to the standard
library function; `PrimitiveContext` states exactly that. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target functionAcceptsAt)
open Solcore.Synthesis.Source.ScalarRenderer (Rendered)

section Generic

variable {render : RenderFn} {admits : Context → Prop} {called : List String}

/-- A snapshot of a rendered Word operand is another rendering of it. -/
theorem snapshot_spec {expression : CoreExpr} {functions locals : List String}
    {indent first : Nat} {value : Rendered}
    (spec : RenderSpec admits called expression .word functions locals indent first value) :
    RenderSpec admits called expression .word functions locals indent first
      (snapshotOf indent value) := by
  obtain ⟨statements, lines, le, valueClassified, names, simulates⟩ := spec
  unfold RenderSpec snapshotOf
  dsimp only
  refine ⟨statements ++ [.letDecl (temporary value.nextId) .word (.name value.value)], ?_,
    by omega, Or.inr (allocated_temporary le (Nat.lt_succ_self _)), ?_, ?_⟩
  · simp only [Stmt.listLines_append, lines, Stmt.listLines, List.append_nil]
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at mem
    rcases mem with mem | same | same
    · exact named_mono (names name mem) (Nat.le_refl _) (by omega)
    · exact named_allocated ⟨value.nextId, same, le, by omega⟩
    · subst same
      exact named_of_classified valueClassified (Nat.le_refl _) (by omega)
  · refine result_simulates (target := .word) (fun context environment store scope outer
      admitted agree lengthOk functionsOk => ?_) le
    obtain ⟨core, source, scope₁, outer₁, added₁, evaluates, represents, exec, lookup, keeps,
      shape, scopeNames, added⟩ :=
      simulates context environment store scope outer admitted agree lengthOk functionsOk
    exact ⟨core, source, scope₁, outer₁, added₁, evaluates, represents, exec, lookup, keeps,
      shape, scopeNames, added⟩

/-- A unary operation printed as one fresh temporary bound to `initializer`,
which reads the operand's value name. -/
theorem unaryResult_spec {op : Solcore.Core.Wire.UnaryOp} {operand : CoreExpr}
    {operandTarget target : Target} {functions locals : List String} {indent first : Nat}
    {value : Rendered} {initializer : Expr}
    (spec : RenderSpec admits called operand operandTarget functions locals indent first value)
    (initializerNames : ∀ name ∈ initializer.identifiers, name = value.value ∨ name ∈ called)
    (agree : ∀ (context : Context) (frames : Frames) (core : CoreValue) (source : Value),
      admits context → frames.lookup value.value = some source →
      Represents operandTarget core source →
      ∃ coreResult sourceResult,
        Solcore.Core.UnaryOp.apply op.toCore core = some coreResult ∧
        initializer.eval context frames = some sourceResult ∧
        Represents target coreResult sourceResult) :
    RenderSpec admits called (.unary op operand) target functions locals indent first
      (resultOf indent target value.lines value.nextId initializer) := by
  obtain ⟨statements, lines, le, valueClassified, names, simulates⟩ := spec
  unfold RenderSpec resultOf
  dsimp only
  refine ⟨statements ++ [.letDecl (temporary value.nextId) (LocalType.ofTarget target)
      initializer], ?_, by omega, Or.inr (allocated_temporary le (Nat.lt_succ_self _)), ?_, ?_⟩
  · simp only [Stmt.listLines_append, lines, Stmt.listLines, List.append_nil]
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, List.append_nil, List.mem_cons] at mem
    rcases mem with mem | same | mem
    · exact named_mono (names name mem) (Nat.le_refl _) (by omega)
    · exact named_allocated ⟨value.nextId, same, le, by omega⟩
    · rcases initializerNames name mem with same | mem
      · subst same
        exact named_of_classified valueClassified (Nat.le_refl _) (by omega)
      · exact Or.inr (Or.inr (Or.inr mem))
  · refine result_simulates (fun context environment store scope outer admitted agreeLocals
      lengthOk functionsOk => ?_) le
    obtain ⟨core, source, scope₁, outer₁, added₁, evaluates, represents, exec, lookup, keeps,
      shape, scopeNames, added⟩ :=
      simulates context environment store scope outer admitted agreeLocals lengthOk functionsOk
    obtain ⟨coreResult, sourceResult, coreApply, initialized, resultRepresents⟩ :=
      agree context _ core source admitted lookup represents
    refine ⟨coreResult, sourceResult, scope₁, outer₁, added₁, ?_, resultRepresents, exec,
      initialized, keeps, shape, scopeNames, added⟩
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .unary evaluates coreApply

/-- A binary operation printed as one fresh temporary bound to `initializer`,
which reads the two operands' value names. -/
theorem binaryResult_spec {op : Solcore.Core.Wire.BinaryOp} {left right : CoreExpr}
    {target : Target} {functions locals : List String} {indent first : Nat}
    {leftValue rightValue : Rendered} {initializer : Expr}
    (fresh : ∀ name ∈ locals, OlderThan first name)
    (leftSpec : RenderSpec admits called left .word functions locals indent first leftValue)
    (rightSpec : RenderSpec admits called right .word functions locals indent leftValue.nextId
      rightValue)
    (initializerNames : ∀ name ∈ initializer.identifiers,
      name = leftValue.value ∨ name = rightValue.value ∨ name ∈ called)
    (agree : ∀ (context : Context) (frames : Frames) (leftWord rightWord : Solcore.Core.Word),
      admits context → frames.lookup leftValue.value = some (.word leftWord.val) →
      frames.lookup rightValue.value = some (.word rightWord.val) →
      ∃ coreResult sourceResult,
        Solcore.Core.BinaryOp.apply op.toCore (.word leftWord) (.word rightWord) =
          some coreResult ∧
        initializer.eval context frames = some sourceResult ∧
        Represents target coreResult sourceResult) :
    RenderSpec admits called (.binary op left right) target functions locals indent first
      (resultOf indent target (leftValue.lines ++ rightValue.lines) rightValue.nextId
        initializer) := by
  obtain ⟨leftStatements, leftLines, leftLe, leftValueName, leftNames, leftSimulates⟩ :=
    leftSpec
  obtain ⟨rightStatements, rightLines, rightLe, rightValueName, rightNames, rightSimulates⟩ :=
    rightSpec
  unfold RenderSpec resultOf
  dsimp only
  refine ⟨leftStatements ++ rightStatements ++ [.letDecl (temporary rightValue.nextId)
      (LocalType.ofTarget target) initializer], ?_, by omega,
    Or.inr (allocated_temporary (by omega) (Nat.lt_succ_self _)), ?_, ?_⟩
  · simp only [Stmt.listLines_append, leftLines, rightLines, Stmt.listLines, List.append_nil]
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, List.append_nil, List.mem_cons] at mem
    rcases mem with (mem | mem) | same | mem
    · exact named_mono (leftNames name mem) (Nat.le_refl _) (by omega)
    · exact named_mono (rightNames name mem) leftLe (by omega)
    · exact named_allocated ⟨rightValue.nextId, same, by omega, by omega⟩
    · rcases initializerNames name mem with same | same | mem
      · subst same
        exact named_of_classified leftValueName (Nat.le_refl _) (by omega)
      · subst same
        exact named_of_classified rightValueName leftLe (by omega)
      · exact Or.inr (Or.inr (Or.inr mem))
  · refine result_simulates (fun context environment store scope outer admitted agreeLocals
      lengthOk functionsOk => ?_) (by omega)
    obtain ⟨leftCore, leftSource, scope₁, outer₁, added₁, leftEvaluates, leftRepresents,
      leftExec, leftLookup, leftKeeps, leftShape, leftScope, leftAdded⟩ :=
      leftSimulates context environment store scope outer admitted agreeLocals lengthOk
        functionsOk
    have rightAgree : LocalsAgree (scope₁ :: outer₁) locals environment :=
      agreeLocals.transfer fun name mem =>
        leftKeeps name (not_allocated_of_older (fresh name mem) (Nat.le_refl first))
    obtain ⟨rightCore, rightSource, scope₂, outer₂, added₂, rightEvaluates, rightRepresents,
      rightExec, rightLookup, rightKeeps, rightShape, rightScope, rightAdded⟩ :=
      rightSimulates context environment store scope₁ outer₁ admitted rightAgree lengthOk
        functionsOk
    obtain ⟨leftWord, rfl, rfl⟩ := leftRepresents
    obtain ⟨rightWord, rfl, rfl⟩ := rightRepresents
    have leftSurvives :
        Frames.lookup (scope₂ :: outer₂) leftValue.value = some (.word leftWord.val) := by
      rw [rightKeeps _ (value_not_reallocated fresh leftLe leftValueName)]
      exact leftLookup
    obtain ⟨coreResult, sourceResult, coreApply, initialized, resultRepresents⟩ :=
      agree context _ leftWord rightWord admitted leftSurvives rightLookup
    refine ⟨coreResult, sourceResult, scope₂, outer₂, added₂ ++ added₁, ?_, resultRepresents,
      ?_, initialized, ?_, rightShape.trans leftShape, ?_, ?_⟩
    · simp only [Solcore.Core.Wire.Expr.toCore]
      exact .binary leftEvaluates rightEvaluates coreApply
    · rw [Stmt.execList_append, leftExec]
      simpa using rightExec
    · intro name notAllocated
      rw [rightKeeps name fun allocated =>
          notAllocated (allocated_mono allocated leftLe (Nat.le_refl _)),
        leftKeeps name fun allocated =>
          notAllocated (allocated_mono allocated (Nat.le_refl _) rightLe)]
    · rw [rightScope, leftScope]
      simp
    · intro name mem
      rcases List.mem_append.mp mem with mem | mem
      · exact allocated_mono (rightAdded name mem) leftLe (Nat.le_refl _)
      · exact allocated_mono (leftAdded name mem) (Nat.le_refl _) rightLe

/-- A ternary operation printed as one fresh temporary bound to
`initializer`, which reads the three operands' value names. -/
theorem ternaryResult_spec {op : Solcore.Core.Wire.TernaryOp} {one two three : CoreExpr}
    {target : Target} {functions locals : List String} {indent first : Nat}
    {oneValue twoValue threeValue : Rendered} {initializer : Expr}
    (fresh : ∀ name ∈ locals, OlderThan first name)
    (oneSpec : RenderSpec admits called one .word functions locals indent first oneValue)
    (twoSpec : RenderSpec admits called two .word functions locals indent oneValue.nextId
      twoValue)
    (threeSpec : RenderSpec admits called three .word functions locals indent twoValue.nextId
      threeValue)
    (initializerNames : ∀ name ∈ initializer.identifiers,
      name = oneValue.value ∨ name = twoValue.value ∨ name = threeValue.value ∨ name ∈ called)
    (agree : ∀ (context : Context) (frames : Frames)
      (oneWord twoWord threeWord : Solcore.Core.Word),
      admits context → frames.lookup oneValue.value = some (.word oneWord.val) →
      frames.lookup twoValue.value = some (.word twoWord.val) →
      frames.lookup threeValue.value = some (.word threeWord.val) →
      ∃ coreResult sourceResult,
        Solcore.Core.TernaryOp.apply op.toCore (.word oneWord) (.word twoWord)
          (.word threeWord) = some coreResult ∧
        initializer.eval context frames = some sourceResult ∧
        Represents target coreResult sourceResult) :
    RenderSpec admits called (.ternary op one two three) target functions locals indent first
      (resultOf indent target (oneValue.lines ++ twoValue.lines ++ threeValue.lines)
        threeValue.nextId initializer) := by
  obtain ⟨oneStatements, oneLines, oneLe, oneName, oneNames, oneSimulates⟩ := oneSpec
  obtain ⟨twoStatements, twoLines, twoLe, twoName, twoNames, twoSimulates⟩ := twoSpec
  obtain ⟨threeStatements, threeLines, threeLe, threeName, threeNames, threeSimulates⟩ :=
    threeSpec
  unfold RenderSpec resultOf
  dsimp only
  refine ⟨oneStatements ++ twoStatements ++ threeStatements ++
      [.letDecl (temporary threeValue.nextId) (LocalType.ofTarget target) initializer], ?_,
    by omega, Or.inr (allocated_temporary (by omega) (Nat.lt_succ_self _)), ?_, ?_⟩
  · simp only [Stmt.listLines_append, oneLines, twoLines, threeLines, Stmt.listLines,
      List.append_nil]
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, List.append_nil, List.mem_cons] at mem
    rcases mem with ((mem | mem) | mem) | same | mem
    · exact named_mono (oneNames name mem) (Nat.le_refl _) (by omega)
    · exact named_mono (twoNames name mem) oneLe (by omega)
    · exact named_mono (threeNames name mem) (by omega) (by omega)
    · exact named_allocated ⟨threeValue.nextId, same, by omega, by omega⟩
    · rcases initializerNames name mem with same | same | same | mem
      · subst same
        exact named_of_classified oneName (Nat.le_refl _) (by omega)
      · subst same
        exact named_of_classified twoName oneLe (by omega)
      · subst same
        exact named_of_classified threeName (by omega) (by omega)
      · exact Or.inr (Or.inr (Or.inr mem))
  · refine result_simulates (fun context environment store scope outer admitted agreeLocals
      lengthOk functionsOk => ?_) (by omega)
    obtain ⟨oneCore, oneSource, scope₁, outer₁, added₁, oneEvaluates, oneRepresents,
      oneExec, oneLookup, oneKeeps, oneShape, oneScope, oneAdded⟩ :=
      oneSimulates context environment store scope outer admitted agreeLocals lengthOk
        functionsOk
    have twoAgree : LocalsAgree (scope₁ :: outer₁) locals environment :=
      agreeLocals.transfer fun name mem =>
        oneKeeps name (not_allocated_of_older (fresh name mem) (Nat.le_refl first))
    obtain ⟨twoCore, twoSource, scope₂, outer₂, added₂, twoEvaluates, twoRepresents,
      twoExec, twoLookup, twoKeeps, twoShape, twoScope, twoAdded⟩ :=
      twoSimulates context environment store scope₁ outer₁ admitted twoAgree lengthOk
        functionsOk
    have threeAgree : LocalsAgree (scope₂ :: outer₂) locals environment :=
      twoAgree.transfer fun name mem =>
        twoKeeps name (not_allocated_of_older (fresh name mem) oneLe)
    obtain ⟨threeCore, threeSource, scope₃, outer₃, added₃, threeEvaluates, threeRepresents,
      threeExec, threeLookup, threeKeeps, threeShape, threeScope, threeAdded⟩ :=
      threeSimulates context environment store scope₂ outer₂ admitted threeAgree lengthOk
        functionsOk
    obtain ⟨oneWord, rfl, rfl⟩ := oneRepresents
    obtain ⟨twoWord, rfl, rfl⟩ := twoRepresents
    obtain ⟨threeWord, rfl, rfl⟩ := threeRepresents
    have oneSurvives :
        Frames.lookup (scope₃ :: outer₃) oneValue.value = some (.word oneWord.val) := by
      rw [threeKeeps _ (value_not_reallocated fresh (by omega)
          (classified_mono oneName (Nat.le_refl _) twoLe)),
        twoKeeps _ (value_not_reallocated fresh oneLe oneName)]
      exact oneLookup
    have twoSurvives :
        Frames.lookup (scope₃ :: outer₃) twoValue.value = some (.word twoWord.val) := by
      rw [threeKeeps _ (value_not_reallocated (fun name mem => older_mono (fresh name mem) oneLe)
        twoLe twoName)]
      exact twoLookup
    obtain ⟨coreResult, sourceResult, coreApply, initialized, resultRepresents⟩ :=
      agree context _ oneWord twoWord threeWord admitted oneSurvives twoSurvives threeLookup
    refine ⟨coreResult, sourceResult, scope₃, outer₃, added₃ ++ added₂ ++ added₁, ?_,
      resultRepresents, ?_, initialized, ?_, threeShape.trans (twoShape.trans oneShape), ?_, ?_⟩
    · simp only [Solcore.Core.Wire.Expr.toCore]
      exact .ternary oneEvaluates twoEvaluates threeEvaluates coreApply
    · rw [Stmt.execList_append, Stmt.execList_append, oneExec]
      simpa [twoExec] using threeExec
    · intro name notAllocated
      rw [threeKeeps name fun allocated =>
          notAllocated (allocated_mono allocated (by omega) (Nat.le_refl _)),
        twoKeeps name fun allocated =>
          notAllocated (allocated_mono allocated oneLe (by omega)),
        oneKeeps name fun allocated =>
          notAllocated (allocated_mono allocated (Nat.le_refl _) (by omega))]
    · rw [threeScope, twoScope, oneScope]
      simp
    · intro name mem
      simp only [List.mem_append] at mem
      rcases mem with (mem | mem) | mem
      · exact allocated_mono (threeAdded name mem) (by omega) (Nat.le_refl _)
      · exact allocated_mono (twoAdded name mem) oneLe (by omega)
      · exact allocated_mono (oneAdded name mem) (Nat.le_refl _) (by omega)

/-! ### How a renderer prints raw opcode calls -/

def ClzInversion (render : RenderFn) : Prop :=
  ∀ (functions : List String) (target : Target) (locals : List String) (indent first : Nat)
    (operand : CoreExpr) (rendered : Rendered),
    render functions target locals indent first (.unary .wordClz operand) = .ok rendered →
    ∃ value, render functions .word locals indent first operand = .ok value ∧
      rendered = resultOf indent target (snapshotOf indent value).lines (value.nextId + 1)
        (.call1 "sc_clz" (.name (temporary value.nextId)))

def PrimitiveBinaryInversion (render : RenderFn) : Prop :=
  ∀ (functions : List String) (target : Target) (locals : List String) (indent first : Nat)
    (op : Solcore.Core.Wire.BinaryOp) (build : String → String → Expr) (left right : CoreExpr)
    (rendered : Rendered),
    primitiveBinary? op = some build →
    render functions target locals indent first (.binary op left right) = .ok rendered →
    ∃ leftValue rightValue, render functions .word locals indent first left = .ok leftValue ∧
      render functions .word locals indent (leftValue.nextId + 1) right = .ok rightValue ∧
      rendered = resultOf indent target
        ((snapshotOf indent leftValue).lines ++ (snapshotOf indent rightValue).lines)
        (rightValue.nextId + 1) (build (temporary leftValue.nextId) (temporary rightValue.nextId))

def TernaryInversion (render : RenderFn) : Prop :=
  ∀ (functions : List String) (target : Target) (locals : List String) (indent first : Nat)
    (op : Solcore.Core.Wire.TernaryOp) (one two three : CoreExpr) (rendered : Rendered),
    render functions target locals indent first (.ternary op one two three) = .ok rendered →
    ∃ oneValue twoValue threeValue,
      render functions .word locals indent first one = .ok oneValue ∧
      render functions .word locals indent (oneValue.nextId + 1) two = .ok twoValue ∧
      render functions .word locals indent (twoValue.nextId + 1) three = .ok threeValue ∧
      rendered = resultOf indent target
        ((snapshotOf indent oneValue).lines ++ (snapshotOf indent twoValue).lines ++
          (snapshotOf indent threeValue).lines)
        (threeValue.nextId + 1)
        (.call3 (ternaryCallee op) (.name (temporary oneValue.nextId))
          (.name (temporary twoValue.nextId)) (.name (temporary threeValue.nextId)))

theorem snapshot_le {expression : CoreExpr} {functions locals : List String}
    {indent first : Nat} {value : Rendered}
    (spec : RenderSpec admits called expression .word functions locals indent first
      (snapshotOf indent value)) : first ≤ value.nextId + 1 := by
  obtain ⟨_, _, le, _⟩ := spec
  exact le

theorem renderIH_clz (inversion : ClzInversion render) (calls : "sc_clz" ∈ called)
    (reaches : ∀ context, admits context → ∀ arguments,
      context.call "sc_clz" arguments = opcodeMeaning "clz" arguments)
    {operand : CoreExpr} (operandIH : RenderIH render admits called operand) :
    RenderIH render admits called (.unary .wordClz operand) := by
  intro functions depth prior target locals indent first rendered accepted equation fresh
  simp only [functionAcceptsAt, Target.unaryResult, Target.unaryOperand, Bool.and_eq_true,
    target_beq_iff] at accepted
  obtain ⟨rfl, operandAccepted⟩ := accepted
  obtain ⟨value, valueEquation, rfl⟩ :=
    inversion functions .word locals indent first operand rendered equation
  refine unaryResult_spec (op := .wordClz) (snapshot_spec (operandIH functions depth prior .word
    locals indent first value operandAccepted valueEquation fresh)) ?_ ?_
  · intro name mem
    simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with same | same
    · exact Or.inr (same ▸ calls)
    · exact Or.inl same
  · intro context frames core source admitted lookup represents
    obtain ⟨word, rfl, rfl⟩ := represents
    refine ⟨.word word.clz, .word (Evm.clz word.val), rfl, ?_, word.clz, rfl, by rw [evm_clz]⟩
    simp only [snapshotOf] at lookup
    simp [Expr.eval, lookup, reaches context admitted, opcodeMeaning]

theorem acceptsAt_primitiveBinary {depth prior : Nat} {target : Target}
    {op : Solcore.Core.Wire.BinaryOp} {build : String → String → Expr} {left right : CoreExpr}
    (selected : primitiveBinary? op = some build)
    (accepted : functionAcceptsAt depth prior target (.binary op left right) = true) :
    target = Target.binaryResult op ∧ functionAcceptsAt depth prior .word left = true ∧
      functionAcceptsAt depth prior .word right = true := by
  cases op <;> simp only [primitiveBinary?, reduceCtorEq] at selected <;>
    simp only [functionAcceptsAt, Bool.and_eq_true, target_beq_iff] at accepted <;>
    exact ⟨accepted.1.1, accepted.1.2, accepted.2⟩

theorem renderIH_primitiveBinary (inversion : PrimitiveBinaryInversion render)
    {op : Solcore.Core.Wire.BinaryOp} {build : String → String → Expr}
    (selected : primitiveBinary? op = some build)
    (buildNames : ∀ leftName rightName, ∀ name ∈ (build leftName rightName).identifiers,
      name = leftName ∨ name = rightName ∨ name ∈ called)
    (agree : ∀ (context : Context) (frames : Frames) (leftName rightName : String)
      (left right : Solcore.Core.Word), admits context →
      frames.lookup leftName = some (.word left.val) →
      frames.lookup rightName = some (.word right.val) →
      ∃ coreResult sourceResult,
        Solcore.Core.BinaryOp.apply op.toCore (.word left) (.word right) = some coreResult ∧
        (build leftName rightName).eval context frames = some sourceResult ∧
        Represents (Target.binaryResult op) coreResult sourceResult)
    {left right : CoreExpr} (leftIH : RenderIH render admits called left)
    (rightIH : RenderIH render admits called right) :
    RenderIH render admits called (.binary op left right) := by
  intro functions depth prior target locals indent first rendered accepted equation fresh
  obtain ⟨targetEq, leftAccepted, rightAccepted⟩ := acceptsAt_primitiveBinary selected accepted
  subst targetEq
  obtain ⟨leftValue, rightValue, leftEquation, rightEquation, rfl⟩ :=
    inversion functions _ locals indent first op build left right rendered selected equation
  have leftSpec := snapshot_spec (leftIH functions depth prior .word locals indent first
    leftValue leftAccepted leftEquation fresh)
  have rightSpec := snapshot_spec (rightIH functions depth prior .word locals indent
    (leftValue.nextId + 1) rightValue rightAccepted rightEquation
    (fun name mem => older_mono (fresh name mem) (snapshot_le leftSpec)))
  exact binaryResult_spec fresh leftSpec rightSpec
    (buildNames (temporary leftValue.nextId) (temporary rightValue.nextId))
    (fun context frames leftWord rightWord admitted leftLookup rightLookup =>
      agree context frames _ _ leftWord rightWord admitted leftLookup rightLookup)

theorem renderIH_ternary (inversion : TernaryInversion render)
    {op : Solcore.Core.Wire.TernaryOp} (calls : ternaryCallee op ∈ called)
    (agree : ∀ (context : Context) (frames : Frames) (oneName twoName threeName : String)
      (one two three : Solcore.Core.Word), admits context →
      frames.lookup oneName = some (.word one.val) →
      frames.lookup twoName = some (.word two.val) →
      frames.lookup threeName = some (.word three.val) →
      ∃ coreResult sourceResult,
        Solcore.Core.TernaryOp.apply op.toCore (.word one) (.word two) (.word three) =
          some coreResult ∧
        (Expr.call3 (ternaryCallee op) (.name oneName) (.name twoName) (.name threeName)).eval
          context frames = some sourceResult ∧
        Represents .word coreResult sourceResult)
    {one two three : CoreExpr} (oneIH : RenderIH render admits called one)
    (twoIH : RenderIH render admits called two) (threeIH : RenderIH render admits called three) :
    RenderIH render admits called (.ternary op one two three) := by
  intro functions depth prior target locals indent first rendered accepted equation fresh
  simp only [functionAcceptsAt, Bool.and_eq_true, target_beq_iff] at accepted
  obtain ⟨⟨⟨rfl, oneAccepted⟩, twoAccepted⟩, threeAccepted⟩ := accepted
  obtain ⟨oneValue, twoValue, threeValue, oneEquation, twoEquation, threeEquation, rfl⟩ :=
    inversion functions .word locals indent first op one two three rendered equation
  have oneSpec := snapshot_spec (oneIH functions depth prior .word locals indent first
    oneValue oneAccepted oneEquation fresh)
  have twoSpec := snapshot_spec (twoIH functions depth prior .word locals indent
    (oneValue.nextId + 1) twoValue twoAccepted twoEquation
    (fun name mem => older_mono (fresh name mem) (snapshot_le oneSpec)))
  have threeSpec := snapshot_spec (threeIH functions depth prior .word locals indent
    (twoValue.nextId + 1) threeValue threeAccepted threeEquation
    (fun name mem => older_mono (fresh name mem)
      (Nat.le_trans (snapshot_le oneSpec) (snapshot_le twoSpec))))
  refine ternaryResult_spec fresh oneSpec twoSpec threeSpec ?_
    (fun context frames oneWord twoWord threeWord admitted oneLookup twoLookup threeLookup =>
      agree context frames _ _ _ oneWord twoWord threeWord admitted oneLookup twoLookup
        threeLookup)
  intro name mem
  simp only [Expr.identifiers, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false] at mem
  rcases mem with same | (same | same) | same
  · exact Or.inr (Or.inr (Or.inr (same ▸ calls)))
  · exact Or.inl same
  · exact Or.inr (Or.inl same)
  · exact Or.inr (Or.inr (Or.inl same))

end Generic

/-! ### The actual primitive renderer -/

/-- The primitive renderer with the helper list of the shared signature,
which it does not use. -/
def primitiveRender (_ : List String) (target : Target) (locals : List String)
    (indent first : Nat) (expression : CoreExpr) : Except EmitError Rendered :=
  PrimitiveRenderer.render target locals indent first expression

theorem primitive_word : WordInversion primitiveRender := by
  intro functions target locals indent first value rendered equation
  rw [primitiveRender, PrimitiveEquations.word] at equation
  exact (Except.ok.inj equation).symm

theorem primitive_bool : BoolInversion primitiveRender := by
  intro functions target locals indent first value rendered equation
  rw [primitiveRender, PrimitiveEquations.bool] at equation
  exact (Except.ok.inj equation).symm

theorem primitive_var : VarInversion primitiveRender := by
  intro functions target locals indent first index rendered equation
  rw [primitiveRender, PrimitiveEquations.var] at equation
  cases found : locals[index]? with
  | none =>
      rw [found] at equation
      cases equation
  | some binding =>
      rw [found] at equation
      exact ⟨binding, rfl, (Except.ok.inj equation).symm⟩

theorem primitive_letE : LetInversion primitiveRender := by
  intro functions target locals indent first initializer body rendered equation
  rw [primitiveRender, PrimitiveEquations.letE] at equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rest, restEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨value, rest, valueEquation, restEquation, (Except.ok.inj equation).symm⟩

theorem primitive_ifE : IfInversion primitiveRender := by
  intro functions target locals indent first condition yes no rendered equation
  rw [primitiveRender, PrimitiveEquations.ifE] at equation
  obtain ⟨tested, testedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨selected, selectedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨fallback, fallbackEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨tested, selected, fallback, testedEquation, selectedEquation, fallbackEquation,
    (Except.ok.inj equation).symm⟩

theorem primitive_unary : UnaryInversion primitiveRender := by
  intro functions target locals indent first op sourceOp operand rendered selected equation
  rw [primitiveRender, PrimitiveEquations.unary target locals indent first op sourceOp operand
    selected] at equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨value, valueEquation, (Except.ok.inj equation).symm⟩

theorem primitive_binary : BinaryInversion primitiveRender := by
  intro functions target locals indent first op sourceOp left right rendered selected equation
  rw [primitiveRender, PrimitiveEquations.binary target locals indent first op sourceOp left
    right selected] at equation
  obtain ⟨leftValue, leftEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightValue, rightEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨leftValue, rightValue, leftEquation, rightEquation, (Except.ok.inj equation).symm⟩

theorem primitive_clz : ClzInversion primitiveRender := by
  intro functions target locals indent first operand rendered equation
  rw [primitiveRender, PrimitiveEquations.clz] at equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨value, valueEquation, (Except.ok.inj equation).symm⟩

theorem primitive_primitiveBinary : PrimitiveBinaryInversion primitiveRender := by
  intro functions target locals indent first op build left right rendered selected equation
  rw [primitiveRender, PrimitiveEquations.binary_primitive target locals indent first op build
    left right selected] at equation
  obtain ⟨leftValue, leftEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightValue, rightEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨leftValue, rightValue, leftEquation, rightEquation, (Except.ok.inj equation).symm⟩

theorem primitive_ternary : TernaryInversion primitiveRender := by
  intro functions target locals indent first op one two three rendered equation
  rw [primitiveRender, PrimitiveEquations.ternary] at equation
  obtain ⟨oneValue, oneEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨twoValue, twoEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨threeValue, threeEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨oneValue, twoValue, threeValue, oneEquation, twoEquation, threeEquation,
    (Except.ok.inj equation).symm⟩

/-! ### Calls reaching the raw opcodes -/

/-- A call context in which every primitive alias reaches its `std.opcodes`
instruction and `tobool` is the standard library function. -/
def PrimitiveContext (context : Context) : Prop :=
  (∀ alias ∈ primitiveAliases, ∀ arguments,
      context.call alias.2 arguments = opcodeMeaning alias.1 arguments) ∧
    ∀ arguments, context.call "tobool" arguments = builtinMeaning "tobool" arguments

/-- The callees the primitive renderers print. -/
def primitiveCallees : List String := "tobool" :: primitiveAliases.map Prod.snd

theorem PrimitiveContext.reaches {context : Context} (admitted : PrimitiveContext context)
    {opcode alias : String} (mem : (opcode, alias) ∈ primitiveAliases)
    (arguments : List Value) : context.call alias arguments = opcodeMeaning opcode arguments :=
  admitted.1 (opcode, alias) mem arguments

theorem primitiveBinary_agree {op : Solcore.Core.Wire.BinaryOp}
    {build : String → String → Expr} (selected : primitiveBinary? op = some build)
    (context : Context) (frames : Frames) (leftName rightName : String)
    (left right : Solcore.Core.Word) (admitted : PrimitiveContext context)
    (leftLookup : frames.lookup leftName = some (.word left.val))
    (rightLookup : frames.lookup rightName = some (.word right.val)) :
    ∃ coreResult sourceResult,
      Solcore.Core.BinaryOp.apply op.toCore (.word left) (.word right) = some coreResult ∧
      (build leftName rightName).eval context frames = some sourceResult ∧
      Represents (Target.binaryResult op) coreResult sourceResult := by
  cases op <;> simp only [primitiveBinary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected
  case wordDiv =>
    refine ⟨.word (left.udiv right), .word (Evm.div left.val right.val), rfl, ?_,
      left.udiv right, rfl, by rw [evm_div]⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "div") (alias := "sc_div") (by decide), opcodeMeaning]
  case wordMod =>
    refine ⟨.word (left.umod right), .word (Evm.mod left.val right.val), rfl, ?_,
      left.umod right, rfl, by rw [evm_mod]⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "mod") (alias := "sc_mod") (by decide), opcodeMeaning]
  case wordShl =>
    refine ⟨.word (left.shiftLeft right), .word (Evm.shl right.val left.val), rfl, ?_,
      left.shiftLeft right, rfl, by rw [evm_shl]⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "shl") (alias := "sc_shl") (by decide), opcodeMeaning]
  case wordShr =>
    refine ⟨.word (left.shiftRight right), .word (Evm.shr right.val left.val), rfl, ?_,
      left.shiftRight right, rfl, by rw [evm_shr]⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "shr") (alias := "sc_shr") (by decide), opcodeMeaning]
  case wordSar =>
    refine ⟨.word (left.shiftArithmeticRight right), .word (Evm.sar right.val left.val), rfl,
      ?_, left.shiftArithmeticRight right, rfl, by rw [evm_sar]⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "sar") (alias := "sc_sar") (by decide), opcodeMeaning]
  case wordSdiv =>
    refine ⟨.word (left.sdiv right), .word (Evm.sdiv left.val right.val), rfl, ?_,
      left.sdiv right, rfl, by rw [evm_sdiv]⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "sdiv") (alias := "sc_sdiv") (by decide), opcodeMeaning]
  case wordSmod =>
    refine ⟨.word (left.smod right), .word (Evm.smod left.val right.val), rfl, ?_,
      left.smod right, rfl, by rw [evm_smod]⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "smod") (alias := "sc_smod") (by decide), opcodeMeaning]
  case wordSgt =>
    refine ⟨.bool (left.signedGt right), .bool (toBool (Evm.sgt left.val right.val)), rfl, ?_,
      left.signedGt right, rfl, congrArg Value.bool (evm_sgt left right)⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "sgt") (alias := "sc_sgt") (by decide), opcodeMeaning,
      admitted.2, builtinMeaning]
  case wordByte =>
    refine ⟨.word (left.byteAt right), .word (Evm.byte left.val right.val), rfl, ?_,
      left.byteAt right, rfl, by rw [evm_byte]⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "byte") (alias := "sc_byte") (by decide), opcodeMeaning]
  case wordPow =>
    refine ⟨.word (left.pow right), .word (Evm.exp left.val right.val), rfl, ?_,
      left.pow right, rfl, by rw [evm_exp]⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "exp") (alias := "sc_exp") (by decide), opcodeMeaning]
  case wordSignExtend =>
    refine ⟨.word (left.signExtend right), .word (Evm.signextend left.val right.val), rfl, ?_,
      left.signExtend right, rfl, by rw [evm_signextend]⟩
    simp [Expr.eval, leftLookup, rightLookup,
      admitted.reaches (opcode := "signextend") (alias := "sc_signextend") (by decide),
      opcodeMeaning]

theorem ternary_agree (op : Solcore.Core.Wire.TernaryOp) (context : Context)
    (frames : Frames) (oneName twoName threeName : String) (one two three : Solcore.Core.Word)
    (admitted : PrimitiveContext context)
    (oneLookup : frames.lookup oneName = some (.word one.val))
    (twoLookup : frames.lookup twoName = some (.word two.val))
    (threeLookup : frames.lookup threeName = some (.word three.val)) :
    ∃ coreResult sourceResult,
      Solcore.Core.TernaryOp.apply op.toCore (.word one) (.word two) (.word three) =
        some coreResult ∧
      (Expr.call3 (ternaryCallee op) (.name oneName) (.name twoName) (.name threeName)).eval
        context frames = some sourceResult ∧
      Represents .word coreResult sourceResult := by
  cases op
  case wordAddMod =>
    refine ⟨.word (one.addMod two three), .word (Evm.addmod one.val two.val three.val), rfl, ?_,
      one.addMod two three, rfl, by rw [evm_addmod]⟩
    simp [Expr.eval, oneLookup, twoLookup, threeLookup, ternaryCallee,
      admitted.reaches (opcode := "addmod") (alias := "sc_addmod") (by decide), opcodeMeaning]
  case wordMulMod =>
    refine ⟨.word (one.mulMod two three), .word (Evm.mulmod one.val two.val three.val), rfl, ?_,
      one.mulMod two three, rfl, by rw [evm_mulmod]⟩
    simp [Expr.eval, oneLookup, twoLookup, threeLookup, ternaryCallee,
      admitted.reaches (opcode := "mulmod") (alias := "sc_mulmod") (by decide), opcodeMeaning]

theorem primitiveBinary_names {op : Solcore.Core.Wire.BinaryOp}
    {build : String → String → Expr} (selected : primitiveBinary? op = some build)
    (leftName rightName : String) :
    ∀ name ∈ (build leftName rightName).identifiers,
      name = leftName ∨ name = rightName ∨ name ∈ primitiveCallees := by
  intro name mem
  cases op <;> simp only [primitiveBinary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;>
    simp only [Expr.identifiers, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at mem <;>
    rcases mem with rfl | rfl | rfl | rfl <;> simp [primitiveCallees, primitiveAliases]

theorem primitive_unary_spec {op : Solcore.Core.Wire.UnaryOp} {operand : CoreExpr}
    (operandIH : RenderIH primitiveRender PrimitiveContext primitiveCallees operand) :
    RenderIH primitiveRender PrimitiveContext primitiveCallees (.unary op operand) := by
  cases selected : sourceUnary? op with
  | some _ => exact renderIH_unary primitive_unary selected operandIH
  | none =>
      cases op
      case boolNot => simp [sourceUnary?] at selected
      case wordNot => simp [sourceUnary?] at selected
      case wordClz =>
        exact renderIH_clz primitive_clz (by decide)
          (fun _ admitted => admitted.reaches (by decide)) operandIH
      all_goals
        refine renderIH_error _ fun functions target locals indent first rendered equation => ?_
        rw [primitiveRender, PrimitiveEquations.unary_unsupported _ _ _ _ _ _ rfl] at equation
        cases equation

theorem primitive_binary_spec {op : Solcore.Core.Wire.BinaryOp} {left right : CoreExpr}
    (leftIH : RenderIH primitiveRender PrimitiveContext primitiveCallees left)
    (rightIH : RenderIH primitiveRender PrimitiveContext primitiveCallees right) :
    RenderIH primitiveRender PrimitiveContext primitiveCallees (.binary op left right) := by
  cases selected : sourceBinary? op with
  | some _ => exact renderIH_binary primitive_binary selected leftIH rightIH
  | none =>
      cases extended : primitiveBinary? op with
      | some build =>
          exact renderIH_primitiveBinary primitive_primitiveBinary extended
            (primitiveBinary_names extended)
            (fun context frames leftName rightName leftWord rightWord admitted =>
              primitiveBinary_agree extended context frames leftName rightName leftWord
                rightWord admitted)
            leftIH rightIH
      | none =>
          refine renderIH_error _ fun functions target locals indent first rendered equation => ?_
          have unsupported : PrimitiveRenderer.supportedBinary op = false := by
            cases op <;> simp_all [sourceBinary?, primitiveBinary?,
              PrimitiveRenderer.supportedBinary, Source.supportedBinary]
          rw [primitiveRender, PrimitiveEquations.binary_unsupported _ _ _ _ _ _ _ unsupported]
            at equation
          cases equation

/-- Every admitted expression that the actual primitive renderer accepts
satisfies its rendering specification in every primitive call context. -/
theorem primitive_render_spec :
    (expression : CoreExpr) →
      RenderIH primitiveRender PrimitiveContext primitiveCallees expression
  | .word value => renderIH_word primitive_word value
  | .bool value => renderIH_bool primitive_bool value
  | .var index => renderIH_var primitive_var index
  | .letE initializer body =>
      renderIH_letE primitive_letE (primitive_render_spec initializer)
        (primitive_render_spec body)
  | .ifE condition yes no =>
      renderIH_ifE primitive_ifE (primitive_render_spec condition) (primitive_render_spec yes)
        (primitive_render_spec no)
  | .unary _ operand => primitive_unary_spec (primitive_render_spec operand)
  | .binary _ left right =>
      primitive_binary_spec (primitive_render_spec left) (primitive_render_spec right)
  | .ternary op one two three =>
      renderIH_ternary primitive_ternary (by cases op <;> decide)
        (fun context frames oneName twoName threeName oneWord twoWord threeWord admitted =>
          ternary_agree op context frames oneName twoName threeName oneWord twoWord threeWord
            admitted)
        (primitive_render_spec one) (primitive_render_spec two) (primitive_render_spec three)
  | .apply _ _ =>
      renderIH_error _ fun _ _ _ _ _ _ equation => by
        rw [primitiveRender] at equation
        cases equation
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

import Solcore.Synthesis.Source.ScalarMeaning.AggregateCallGraphEquations

/-! Meaning preservation for the actual `AggregateCallGraphRenderer.render`. Its
bindings are a subset of the aggregate renderer's, so its rendering
specification is the aggregate one over the translated bindings. The emitter
always imports the raw opcode aliases, so every body runs in a primitive call
context. Each case applies the renderer-independent combinators of
`AggregatePreservation` and `AggregateControl`; this renderer has no cells,
no Unit values, and snapshots a helper call's argument before the call. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target)
open Solcore.Synthesis.Core.Aggregates (Local initializerKind? infer?)

/-- What the induction establishes for one expression: a successful rendering
is at a value type and satisfies the aggregate rendering specification over
the translated bindings. -/
def GRenderIH (expression : CoreExpr) : Prop :=
  ∀ (functions : List String) (target : ATarget) (bindings : List GBinding) (indent first : Nat)
    (rendered : ScalarRenderer.Rendered),
    initializerKind? (bindings.map AggregateCallGraphRenderer.Binding.kind) functions.length
      expression = some target.toLocal →
    AggregateCallGraphRenderer.render functions target bindings indent first expression =
      .ok rendered →
    ANamesFresh (bindings.map GBinding.toAggregate) first →
    ANamesDistinct (bindings.map GBinding.toAggregate) →
    target ≠ .unit ∧
      ARenderSpec PrimitiveContext expression target functions
        (bindings.map GBinding.toAggregate) indent first (ARendered.ofScalar rendered)

theorem gvalueBinding_kind {kind : ATarget} (valued : kind ≠ .unit) (name : String) :
    (gvalueBinding kind name).kind = kind.toLocal := by
  cases kind
  case unit => exact absurd rfl valued
  all_goals rfl

/-! ### Literals and locals -/

theorem gRenderIH_word (value : Solcore.Core.Word) : GRenderIH (.word value) := by
  intro functions target bindings indent first rendered accepted equation fresh _
  have targetWord : target = .word := by
    cases target <;> first | rfl | cases accepted
  subst targetWord
  rw [AggregateCallGraphEquations.word] at equation
  cases equation
  exact ⟨by simp, aleaf_spec (target := .word) (initializer := .number value.val) fresh
    (fun _ mem => by simp [Expr.identifiers] at mem)
    (fun _ _ store _ _ => ⟨.word value, .word value.val, by
      simp only [Solcore.Core.Wire.Expr.toCore]; exact .word,
      by simp [Expr.eval, word_lt_modulus], value, rfl, rfl⟩)⟩

theorem gRenderIH_bool (value : Bool) : GRenderIH (.bool value) := by
  intro functions target bindings indent first rendered accepted equation fresh _
  have targetBool : target = .bool := by
    cases target <;> first | rfl | cases accepted
  subst targetBool
  rw [AggregateCallGraphEquations.bool] at equation
  cases equation
  exact ⟨by simp, aleaf_spec (target := .bool) (initializer := .bool value) fresh
    (fun _ mem => by simp [Expr.identifiers] at mem)
    (fun _ _ store _ _ => ⟨.bool value, .bool value, by
      simp only [Solcore.Core.Wire.Expr.toCore]; exact .bool, rfl, value, rfl, rfl⟩)⟩

theorem gRenderIH_var (index : Nat) : GRenderIH (.var index) := by
  intro functions target bindings indent first rendered _ equation _ _
  obtain ⟨name, valued, found, rfl⟩ := AggregateCallGraphEquations.var_ok equation
  have found' : (bindings.map GBinding.toAggregate)[index]? =
      some (valueBinding target name) := by
    rw [List.getElem?_map, found]
    simp [gvalueBinding_toAggregate valued]
  refine ⟨valued, [], rfl, Nat.le_refl _, ?_, by simp [Stmt.listIdentifiers], ?_⟩
  · intro value same
    cases same
    exact Or.inl ⟨index, target, valued, found'⟩
  · refine asimulates_nil fun environment store scope outer agree => ?_
    obtain ⟨core, inEnvironment, holds⟩ := agree index _ found'
    rw [valueBinding_holds valued] at holds
    refine ⟨core, ?_, by simpa [ARendered.ofScalar] using holds⟩
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .var inEnvironment

/-! ### Local bindings and control -/

theorem gRenderIH_letE {initializer body : CoreExpr} (initializerIH : GRenderIH initializer)
    (bodyIH : GRenderIH body) : GRenderIH (.letE initializer body) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨kind, initializerKind, bodyKind, _⟩ := AggregateKinds.letE accepted
  obtain ⟨kindTarget, value, rest, unitKind, inferred, initialEquation, restEquation, rfl⟩ :=
    AggregateCallGraphEquations.letE_ok equation
  have sameKind : kind = kindTarget.toLocal := by
    have toLocal := AggregateKinds.infer_toLocal inferred
    rw [initializerKind] at toLocal
    exact Option.some.inj toLocal
  subst sameKind
  obtain ⟨_, initSpec⟩ := initializerIH functions kindTarget bindings indent first value
    initializerKind initialEquation fresh distinct
  have initLe : first ≤ value.nextId := initSpec.le
  have mapped : (gvalueBinding kindTarget (temporary value.nextId) :: bindings).map
      GBinding.toAggregate =
      valueBinding kindTarget (temporary value.nextId) :: bindings.map GBinding.toAggregate := by
    simp [gvalueBinding_toAggregate unitKind]
  have bodyFresh : ANamesFresh ((gvalueBinding kindTarget (temporary value.nextId) ::
      bindings).map GBinding.toAggregate) (value.nextId + 1) := by
    rw [mapped]
    refine fresh.cons (Nat.le_succ_of_le initLe) fun name same => ?_
    rw [valueBinding_name unitKind] at same
    cases same
    exact temporary_fresh _
  have bodyDistinct : ANamesDistinct ((gvalueBinding kindTarget (temporary value.nextId) ::
      bindings).map GBinding.toAggregate) := by
    rw [mapped]
    exact distinct.cons fresh fun name same => by
      rw [valueBinding_name unitKind] at same
      cases same
      exact ⟨value.nextId, Or.inl rfl, initLe⟩
  have bodyKind' : initializerKind? ((gvalueBinding kindTarget (temporary value.nextId) ::
      bindings).map AggregateCallGraphRenderer.Binding.kind) functions.length body =
        some target.toLocal := by
    simpa [gvalueBinding_kind unitKind] using bodyKind
  obtain ⟨valued, bodySpec⟩ := bodyIH functions target
    (gvalueBinding kindTarget (temporary value.nextId) :: bindings) indent (value.nextId + 1)
    rest bodyKind' restEquation bodyFresh bodyDistinct
  rw [mapped] at bodySpec
  exact ⟨valued, aletValue_spec unitKind fresh initSpec rfl bodySpec⟩

theorem gRenderIH_ifE {condition yes no : CoreExpr} (conditionIH : GRenderIH condition)
    (yesIH : GRenderIH yes) (noIH : GRenderIH no) : GRenderIH (.ifE condition yes no) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨conditionKind, yesKind, noKind, _⟩ := AggregateKinds.ifE accepted
  obtain ⟨tested, selected, fallback, testedEquation, selectedEquation, fallbackEquation,
    shape⟩ := AggregateCallGraphEquations.ifE_ok equation
  obtain ⟨_, conditionSpec⟩ := conditionIH functions .bool bindings indent first tested
    conditionKind testedEquation fresh distinct
  have conditionLe : first ≤ tested.nextId := conditionSpec.le
  obtain ⟨valued, yesSpec⟩ := yesIH functions target bindings (indent + 4) (tested.nextId + 1)
    selected yesKind selectedEquation (fresh.mono (by omega)) distinct
  have yesLe : tested.nextId + 1 ≤ selected.nextId := yesSpec.le
  obtain ⟨_, noSpec⟩ := noIH functions target bindings (indent + 4) selected.nextId fallback
    noKind fallbackEquation (fresh.mono (by omega)) distinct
  rw [shape valued]
  exact ⟨valued, aifValue_spec valued fresh distinct conditionSpec rfl yesSpec rfl noSpec rfl⟩

theorem gRenderIH_caseE {scrutinee yes no : CoreExpr} (scrutineeIH : GRenderIH scrutinee)
    (yesIH : GRenderIH yes) (noIH : GRenderIH no) : GRenderIH (.caseE scrutinee yes no) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨scrutineeKind, yesKind, noKind, _⟩ := AggregateKinds.caseE accepted
  obtain ⟨tested, selected, fallback, testedEquation, selectedEquation, fallbackEquation,
    shape⟩ := AggregateCallGraphEquations.caseE_ok equation
  obtain ⟨_, scrutineeSpec⟩ := scrutineeIH functions .wordSum bindings indent first tested
    scrutineeKind testedEquation fresh distinct
  have sLe : first ≤ tested.nextId := scrutineeSpec.le
  obtain ⟨valued, yesSpec⟩ := yesIH functions target
    (.word (payloadTemp (tested.nextId + 1)) :: bindings) (indent + 8) (tested.nextId + 2)
    selected yesKind selectedEquation (payload_fresh fresh (by omega))
    (payload_distinct fresh distinct (by omega))
  have yLe : tested.nextId + 2 ≤ selected.nextId := yesSpec.le
  obtain ⟨_, noSpec⟩ := noIH functions target (.word (payloadTemp selected.nextId) :: bindings)
    (indent + 8) (selected.nextId + 1) fallback noKind fallbackEquation
    (payload_fresh fresh (by omega)) (payload_distinct fresh distinct (by omega))
  rw [shape valued]
  exact ⟨valued, acaseValue_spec valued fresh distinct scrutineeSpec rfl yesSpec rfl noSpec rfl⟩

/-! ### Operations, pairs, sum constructors and helper calls -/

theorem gRenderIH_unarySource {op : Solcore.Core.Wire.UnaryOp} {sourceOp : UnaryOp}
    {operand : CoreExpr} (selected : sourceUnary? op = some sourceOp)
    (operandIH : GRenderIH operand) : GRenderIH (.unary op operand) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨_, operandKind, resultKind⟩ := AggregateKinds.unary accepted
  have targetEq := atoLocal_scalarKind resultKind
  subst targetEq
  rw [AggregateCallGraphEquations.unary _ _ _ _ selected] at equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  cases equation
  have operandTarget : (if op == .boolNot then (.bool : ATarget) else .word) =
      ATarget.ofScalar (Target.unaryOperand op) := by
    cases op <;> simp_all [sourceUnary?] <;> rfl
  rw [operandTarget] at valueEquation
  obtain ⟨_, spec⟩ := operandIH functions (ATarget.ofScalar (Target.unaryOperand op)) bindings
    indent first value (by rw [ofScalar_toLocal]; exact operandKind) valueEquation fresh
    distinct
  refine ⟨ATarget.ofScalar_ne_unit _, ?_⟩
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

theorem gRenderIH_clz {operand : CoreExpr} (operandIH : GRenderIH operand) :
    GRenderIH (.unary .wordClz operand) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨_, operandKind, resultKind⟩ := AggregateKinds.unary accepted
  have targetEq := atoLocal_scalarKind resultKind
  subst targetEq
  rw [show ATarget.ofScalar (Target.unaryResult .wordClz) = .word from rfl,
    AggregateCallGraphEquations.clz] at equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  cases equation
  obtain ⟨_, spec⟩ := operandIH functions .word bindings indent first value operandKind
    valueEquation fresh distinct
  have snapshot := asnapshot_spec fresh spec
  refine ⟨ATarget.ofScalar_ne_unit _, aoneResult_spec (target := .word) (by simp) fresh snapshot
    rfl (fun name mem => by
      simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with same | same
      · exact Or.inr (Or.inr (same ▸ by simp [primitiveCallees, primitiveAliases]))
      · exact Or.inl same) ?_⟩
  intro context environment store store₁ operandCore frames source admitted _ _ evaluates
    lookup represents
  obtain ⟨word, rfl, rfl⟩ := represents
  refine ⟨.word word.clz, .word (Evm.clz word.val), store₁, ?_, Nat.le_refl _,
    fun _ _ => rfl, ?_, word.clz, rfl, by rw [evm_clz]⟩
  · simp only [Solcore.Core.Wire.Expr.toCore]
    exact .unary evaluates rfl
  · simp only [snapshotOf] at lookup
    simp [Expr.eval, lookup, admitted.reaches (opcode := "clz") (alias := "sc_clz")
      (by decide), opcodeMeaning]

theorem gRenderIH_binarySource {op : Solcore.Core.Wire.BinaryOp} {sourceOp : BinaryOp}
    {left right : CoreExpr} (selected : sourceBinary? op = some sourceOp)
    (leftIH : GRenderIH left) (rightIH : GRenderIH right) :
    GRenderIH (.binary op left right) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨_, leftKind, rightKind, resultKind⟩ := AggregateKinds.binary accepted
  have targetEq := atoLocal_scalarKind resultKind
  subst targetEq
  rw [AggregateCallGraphEquations.binary _ _ _ _ _ selected] at equation
  obtain ⟨leftValue, leftEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightValue, rightEquation, equation⟩ := except_bind_eq_ok equation
  cases equation
  obtain ⟨_, leftSpec⟩ := leftIH functions .word bindings indent first leftValue leftKind
    leftEquation fresh distinct
  obtain ⟨_, rightSpec⟩ := rightIH functions .word bindings indent leftValue.nextId rightValue
    rightKind rightEquation (fresh.mono leftSpec.le) distinct
  refine ⟨ATarget.ofScalar_ne_unit _, ?_⟩
  rw [← ATarget.ofScalar_localType]
  refine atwoResult_spec fresh distinct leftSpec rfl rightSpec rfl
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at mem
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

theorem gRenderIH_binaryPrimitive {op : Solcore.Core.Wire.BinaryOp}
    {build : String → String → Expr} {left right : CoreExpr}
    (selected : primitiveBinary? op = some build)
    (leftIH : GRenderIH left) (rightIH : GRenderIH right) :
    GRenderIH (.binary op left right) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨_, leftKind, rightKind, resultKind⟩ := AggregateKinds.binary accepted
  have targetEq := atoLocal_scalarKind resultKind
  subst targetEq
  rw [AggregateCallGraphEquations.binary_primitive _ _ _ _ _ selected] at equation
  obtain ⟨leftValue, leftEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightValue, rightEquation, equation⟩ := except_bind_eq_ok equation
  cases equation
  obtain ⟨_, leftSpec⟩ := leftIH functions .word bindings indent first leftValue leftKind
    leftEquation fresh distinct
  have leftSnapshot := asnapshot_spec fresh leftSpec
  obtain ⟨_, rightSpec⟩ := rightIH functions .word bindings indent (leftValue.nextId + 1)
    rightValue rightKind rightEquation (fresh.mono leftSnapshot.le) distinct
  have rightSnapshot := asnapshot_spec (fresh.mono leftSnapshot.le) rightSpec
  refine ⟨ATarget.ofScalar_ne_unit _, ?_⟩
  rw [← ATarget.ofScalar_localType]
  refine atwoResult_spec fresh distinct leftSnapshot rfl rightSnapshot rfl
    (primitiveBinary_names selected _ _) ?_
  intro context environment store store₁ store₂ leftWord rightWord frames admitted
    leftEvaluates rightEvaluates leftLookup rightLookup
  obtain ⟨coreResult, sourceResult, coreApply, sourceApply, resultRepresents⟩ :=
    primitiveBinary_agree selected context frames _ _ leftWord rightWord admitted leftLookup
      rightLookup
  refine ⟨coreResult, sourceResult, ?_, sourceApply, AValue.ofScalar_iff.mpr resultRepresents⟩
  simp only [Solcore.Core.Wire.Expr.toCore]
  exact .binary leftEvaluates rightEvaluates coreApply

theorem gRenderIH_ternary {op : Solcore.Core.Wire.TernaryOp} {one two three : CoreExpr}
    (oneIH : GRenderIH one) (twoIH : GRenderIH two) (threeIH : GRenderIH three) :
    GRenderIH (.ternary op one two three) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨oneKind, twoKind, threeKind, resultWord⟩ := AggregateKinds.ternary accepted
  have targetWord : target = .word := by
    cases target <;> first | rfl | cases resultWord
  subst targetWord
  rw [AggregateCallGraphEquations.ternary] at equation
  obtain ⟨oneValue, oneEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨twoValue, twoEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨threeValue, threeEquation, equation⟩ := except_bind_eq_ok equation
  cases equation
  obtain ⟨_, oneSpec⟩ := oneIH functions .word bindings indent first oneValue oneKind
    oneEquation fresh distinct
  have oneSnapshot := asnapshot_spec fresh oneSpec
  obtain ⟨_, twoSpec⟩ := twoIH functions .word bindings indent (oneValue.nextId + 1) twoValue
    twoKind twoEquation (fresh.mono oneSnapshot.le) distinct
  have twoSnapshot := asnapshot_spec (fresh.mono oneSnapshot.le) twoSpec
  obtain ⟨_, threeSpec⟩ := threeIH functions .word bindings indent (twoValue.nextId + 1)
    threeValue threeKind threeEquation
    (fresh.mono (Nat.le_trans oneSnapshot.le twoSnapshot.le)) distinct
  have threeSnapshot :=
    asnapshot_spec (fresh.mono (Nat.le_trans oneSnapshot.le twoSnapshot.le)) threeSpec
  refine ⟨by simp, athreeResult_spec (target := .word) fresh distinct oneSnapshot rfl
    twoSnapshot rfl threeSnapshot rfl ?_ ?_⟩
  · intro name mem
    simp only [Expr.identifiers, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at mem
    rcases mem with same | (same | same) | same
    · refine Or.inr (Or.inr (Or.inr (same ▸ ?_)))
      cases op <;> simp [ternaryCallee, primitiveCallees, primitiveAliases]
    · exact Or.inl same
    · exact Or.inr (Or.inl same)
    · exact Or.inr (Or.inr (Or.inl same))
  · intro context environment store store₁ store₂ store₃ oneWord twoWord threeWord frames
      admitted oneEvaluates twoEvaluates threeEvaluates oneLookup twoLookup threeLookup
    obtain ⟨coreResult, sourceResult, coreApply, sourceApply, resultRepresents⟩ :=
      ternary_agree op context frames _ _ _ oneWord twoWord threeWord admitted oneLookup
        twoLookup threeLookup
    refine ⟨coreResult, sourceResult, ?_, sourceApply, resultRepresents⟩
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .ternary oneEvaluates twoEvaluates threeEvaluates coreApply

theorem gRenderIH_pair {left right : CoreExpr} (leftIH : GRenderIH left)
    (rightIH : GRenderIH right) : GRenderIH (.pair left right) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨leftKind, rightKind, _⟩ := AggregateKinds.pair accepted
  obtain ⟨rfl, leftValue, rightValue, leftEquation, rightEquation, rfl⟩ :=
    AggregateCallGraphEquations.pair_ok equation
  obtain ⟨_, leftSpec⟩ := leftIH functions .word bindings indent first leftValue leftKind
    leftEquation fresh distinct
  obtain ⟨_, rightSpec⟩ := rightIH functions .word bindings indent leftValue.nextId rightValue
    rightKind rightEquation (fresh.mono leftSpec.le) distinct
  refine ⟨by simp, atwoResult_spec (target := .wordPair) fresh distinct leftSpec rfl rightSpec
    rfl (fun name mem => by
      simp only [Expr.identifiers, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at mem
      rcases mem with same | same
      · exact Or.inl same
      · exact Or.inr (Or.inl same)) ?_⟩
  intro context environment store store₁ store₂ leftWord rightWord frames _ leftEvaluates
    rightEvaluates leftLookup rightLookup
  refine ⟨.pair (.word leftWord) (.word rightWord), .pair leftWord.val rightWord.val, ?_, ?_,
    leftWord, rightWord, rfl, rfl⟩
  · simp only [Solcore.Core.Wire.Expr.toCore]
    exact .pair leftEvaluates rightEvaluates
  · simp [Expr.eval, leftLookup, rightLookup]

theorem gRenderIH_inLeft {type : Solcore.Core.Wire.Ty} {payload : CoreExpr}
    (payloadIH : GRenderIH payload) : GRenderIH (.inLeft type payload) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨rfl, payloadKind, _⟩ := AggregateKinds.inLeft accepted
  obtain ⟨rfl, payloadValue, payloadEquation, rfl⟩ :=
    AggregateCallGraphEquations.inLeft_ok equation
  obtain ⟨_, spec⟩ := payloadIH functions .word bindings indent first payloadValue payloadKind
    payloadEquation fresh distinct
  refine ⟨by simp, aoneResult_spec (target := .wordSum) (by simp) fresh spec rfl
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
      exact Or.inl mem) ?_⟩
  intro context environment store store₁ operandCore frames source _ _ _ evaluates lookup
    represents
  obtain ⟨word, rfl, rfl⟩ := represents
  refine ⟨.inLeft (Solcore.Core.Wire.Ty.toCore .word) (.word word), .inl word.val, store₁, ?_,
    Nat.le_refl _, fun _ _ => rfl, by simp [Expr.eval, lookup], Or.inl ⟨_, word, rfl, rfl⟩⟩
  simp only [Solcore.Core.Wire.Expr.toCore]
  exact .inLeft evaluates

theorem gRenderIH_inRight {type : Solcore.Core.Wire.Ty} {payload : CoreExpr}
    (payloadIH : GRenderIH payload) : GRenderIH (.inRight type payload) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨rfl, payloadKind, _⟩ := AggregateKinds.inRight accepted
  obtain ⟨rfl, payloadValue, payloadEquation, rfl⟩ :=
    AggregateCallGraphEquations.inRight_ok equation
  obtain ⟨_, spec⟩ := payloadIH functions .word bindings indent first payloadValue payloadKind
    payloadEquation fresh distinct
  refine ⟨by simp, aoneResult_spec (target := .wordSum) (by simp) fresh spec rfl
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
      exact Or.inl mem) ?_⟩
  intro context environment store store₁ operandCore frames source _ _ _ evaluates lookup
    represents
  obtain ⟨word, rfl, rfl⟩ := represents
  refine ⟨.inRight (Solcore.Core.Wire.Ty.toCore .word) (.word word), .inr word.val, store₁, ?_,
    Nat.le_refl _, fun _ _ => rfl, by simp [Expr.eval, lookup], Or.inr ⟨_, word, rfl, rfl⟩⟩
  simp only [Solcore.Core.Wire.Expr.toCore]
  exact .inRight evaluates

theorem gRenderIH_first {operand : CoreExpr} (operandIH : GRenderIH operand) :
    GRenderIH (.first operand) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨operandKind, _⟩ := AggregateKinds.first accepted
  obtain ⟨rfl, operandValue, operandEquation, rfl⟩ :=
    AggregateCallGraphEquations.first_ok equation
  obtain ⟨_, spec⟩ := operandIH functions .wordPair bindings indent first operandValue
    operandKind operandEquation fresh distinct
  exact ⟨by simp, aprojection_spec true fresh distinct spec rfl fun _ _ _ _ _ evaluates => by
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .first evaluates⟩

theorem gRenderIH_second {operand : CoreExpr} (operandIH : GRenderIH operand) :
    GRenderIH (.second operand) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨operandKind, _⟩ := AggregateKinds.second accepted
  obtain ⟨rfl, operandValue, operandEquation, rfl⟩ :=
    AggregateCallGraphEquations.second_ok equation
  obtain ⟨_, spec⟩ := operandIH functions .wordPair bindings indent first operandValue
    operandKind operandEquation fresh distinct
  exact ⟨by simp, aprojection_spec false fresh distinct spec rfl fun _ _ _ _ _ evaluates => by
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .second evaluates⟩

/-- A direct call to an earlier helper copies its argument first. The helper
cannot reach the caller's frames, and its evaluation keeps every existing
store location. -/
theorem gRenderIH_apply {index : Nat} {argument : CoreExpr} (argumentIH : GRenderIH argument) :
    GRenderIH (.apply (.var index) argument) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨_, _, argumentKind, _⟩ := AggregateKinds.apply accepted
  obtain ⟨rfl, outside, callee, value, found, valueEquation, rfl⟩ :=
    AggregateCallGraphEquations.apply_ok equation
  obtain ⟨_, spec⟩ := argumentIH functions .word bindings indent first value argumentKind
    valueEquation fresh distinct
  have snapshot := asnapshot_spec fresh spec
  refine ⟨by simp, aoneResult_spec (target := .word) (by simp) fresh snapshot rfl
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with same | same
      · exact Or.inr (Or.inl (same ▸ List.mem_of_getElem? found))
      · exact Or.inl same) ?_⟩
  intro context environment store store₁ operandCore frames source _ _ functionsOk evaluates
    lookup represents
  obtain ⟨word, rfl, rfl⟩ := represents
  rw [List.length_map] at functionsOk
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
  · simp only [snapshotOf] at lookup
    simp [Expr.eval, lookup, callResult]

/-! ### The structural induction -/

/-- An expression the actual renderer always rejects. -/
theorem gRenderIH_error (expression : CoreExpr)
    (fails : ∀ (functions : List String) (target : ATarget) (bindings : List GBinding)
      (indent first : Nat) (rendered : ScalarRenderer.Rendered),
      AggregateCallGraphRenderer.render functions target bindings indent first expression ≠
        .ok rendered) :
    GRenderIH expression := by
  intro functions target bindings indent first rendered _ equation
  exact absurd equation (fails functions target bindings indent first rendered)

theorem gRenderIH_rejected (expression : CoreExpr)
    (rejects : expression = .unit ∨ (∃ value, expression = .integer value) ∨
      (∃ parameterType resultType body, expression = .lambda parameterType resultType body) ∨
      (∃ elementType inner, expression = .newCell elementType inner) ∨
      (∃ reference, expression = .loadCell reference) ∨
      (∃ reference value, expression = .storeCell reference value) ∨
      (∃ constructor payload, expression = .construct constructor payload) ∨
      (∃ dataType resultType scrutinee branches,
        expression = .matchData dataType resultType scrutinee branches)) :
    GRenderIH expression :=
  gRenderIH_error _ fun _ _ _ _ _ _ equation =>
    AggregateCallGraphEquations.rejected rejects equation

theorem gRenderIH_unary {op : Solcore.Core.Wire.UnaryOp} {operand : CoreExpr}
    (operandIH : GRenderIH operand) : GRenderIH (.unary op operand) := by
  cases selected : sourceUnary? op with
  | some _ => exact gRenderIH_unarySource selected operandIH
  | none =>
      cases op
      case boolNot => simp [sourceUnary?] at selected
      case wordNot => simp [sourceUnary?] at selected
      case wordClz => exact gRenderIH_clz operandIH
      all_goals
        intro _ _ _ _ _ _ accepted
        exact absurd (AggregateKinds.unary accepted).1 (by simp [MutationKinds.integerUnary])

theorem gRenderIH_binary {op : Solcore.Core.Wire.BinaryOp} {left right : CoreExpr}
    (leftIH : GRenderIH left) (rightIH : GRenderIH right) : GRenderIH (.binary op left right) := by
  cases selected : sourceBinary? op with
  | some _ => exact gRenderIH_binarySource selected leftIH rightIH
  | none =>
      cases extended : primitiveBinary? op with
      | some _ => exact gRenderIH_binaryPrimitive extended leftIH rightIH
      | none =>
          cases op <;> first
            | (simp [sourceBinary?] at selected; done)
            | (simp [primitiveBinary?] at extended; done)
            | (intro _ _ _ _ _ _ accepted
               exact absurd (AggregateKinds.binary accepted).1
                 (by simp [MutationKinds.integerBinary]))

theorem gRenderIH_applyAny {function argument : CoreExpr} (argumentIH : GRenderIH argument) :
    GRenderIH (.apply function argument) := by
  cases function
  case var index => exact gRenderIH_apply argumentIH
  all_goals
    exact gRenderIH_error _ fun _ _ _ _ _ _ equation => by cases equation

/-- Every expression that the aggregate profile accepts and the actual
aggregate call-graph renderer renders is rendered at a value type and
satisfies the aggregate rendering specification in every primitive call
context. -/
theorem aggregateCallGraph_render_spec : (expression : CoreExpr) → GRenderIH expression
  | .word value => gRenderIH_word value
  | .bool value => gRenderIH_bool value
  | .var index => gRenderIH_var index
  | .letE initializer body =>
      gRenderIH_letE (aggregateCallGraph_render_spec initializer)
        (aggregateCallGraph_render_spec body)
  | .ifE condition yes no =>
      gRenderIH_ifE (aggregateCallGraph_render_spec condition)
        (aggregateCallGraph_render_spec yes) (aggregateCallGraph_render_spec no)
  | .pair left right =>
      gRenderIH_pair (aggregateCallGraph_render_spec left) (aggregateCallGraph_render_spec right)
  | .first operand => gRenderIH_first (aggregateCallGraph_render_spec operand)
  | .second operand => gRenderIH_second (aggregateCallGraph_render_spec operand)
  | .inLeft _ payload => gRenderIH_inLeft (aggregateCallGraph_render_spec payload)
  | .inRight _ payload => gRenderIH_inRight (aggregateCallGraph_render_spec payload)
  | .caseE scrutinee yes no =>
      gRenderIH_caseE (aggregateCallGraph_render_spec scrutinee)
        (aggregateCallGraph_render_spec yes) (aggregateCallGraph_render_spec no)
  | .unary _ operand => gRenderIH_unary (aggregateCallGraph_render_spec operand)
  | .binary _ left right =>
      gRenderIH_binary (aggregateCallGraph_render_spec left)
        (aggregateCallGraph_render_spec right)
  | .ternary _ one two three =>
      gRenderIH_ternary (aggregateCallGraph_render_spec one) (aggregateCallGraph_render_spec two)
        (aggregateCallGraph_render_spec three)
  | .apply _ argument => gRenderIH_applyAny (aggregateCallGraph_render_spec argument)
  | .unit => gRenderIH_rejected _ (Or.inl rfl)
  | .integer _ => gRenderIH_rejected _ (Or.inr (Or.inl ⟨_, rfl⟩))
  | .lambda _ _ _ => gRenderIH_rejected _ (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩)))
  | .newCell _ _ => gRenderIH_rejected _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))))
  | .loadCell _ => gRenderIH_rejected _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))
  | .storeCell _ _ =>
      gRenderIH_rejected _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))))))
  | .construct _ _ =>
      gRenderIH_rejected _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))))))
  | .matchData _ _ _ _ =>
      gRenderIH_rejected _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, _, rfl⟩)))))))

end Solcore.Synthesis.Source.ScalarMeaning

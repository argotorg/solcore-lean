import Solcore.SourceSemantics.CoreLowering.AcceptedCalls

/-!
# Accepted bodies: builtin conversions

The conversions of a word, `uintN(w)`, `intN(w)`, and `Typedef.abs` and `Typedef.rep` at `word`,
as compiler sites of named-row bodies: the native check of the lowered word, the compiler's
receipt at a conversion, the rejection of a conversion's callee lowered on its own, and the token
of `DirtyHigherBitsForInteger()`.

Main declarations:
- `CellAwareInvocationAcceptedConversionCode.canonicalWord_beq`, and the evaluation of
  `SourceCoreInteger.conversion` in `CellAwareInvocationAcceptedConversionCode`;
- `CellAwareInvocationAcceptedConversionSites.ConversionSite` and
  `CellAwareInvocationAcceptedConversionSites.of_accepted`, a conversion's receipt;
- `CellAwareInvocationAcceptedConversionSites.ConversionReference` and
  `CellAwareInvocationAcceptedConversionSites.reference_rejected`, its callee;
- `CellAwareInvocationAcceptedConversionFaults.DirtyToken` and
  `CellAwareInvocationAcceptedConversionFaults.dirtyToken`, the token law of a dirty word;
- `CellAwareInvocationAcceptedConversions.preserves` and
  `CellAwareInvocationAcceptedConversions.reflects`, the cell-aware head of a conversion.

`Typedef.rep` at a fixed-width type is not a site yet.
-/

section
/-! The native check of a conversion. `canonicalWord` is the word that
`SourceCoreInteger.canonicalForm` computes: the low bits of an unsigned word and
the sign extension of a signed one. A word equals it exactly when it is
canonical for the type (`canonicalWord_beq`), so the lowered conversion returns
a canonical word and fails with `SourceCorePanics.dirtyReason` on any other. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedConversionCode
open Core Frontend CoreProof

/-- The canonical form of a word for a fixed-width type, as
`SourceCoreInteger.canonicalForm` computes it. -/
def canonicalWord (type : TypeSystem.FixedInteger) (word : Word) : Word :=
  if type.signed then (Word.ofNatModulo (type.width.bits / 8 - 1)).signExtend word
  else word.bitAnd (Word.ofNatModulo (2 ^ type.width.bits - 1))

theorem canonicalForm_evaluates (type : TypeSystem.FixedInteger) {environment : Environment}
    {store : Store} (word : Word) :
    Evaluates (.word word :: environment) store (SourceCoreInteger.canonicalForm type (.var 0))
      (.word (canonicalWord type word)) store := by
  unfold SourceCoreInteger.canonicalForm canonicalWord
  split
  · exact .binary .word (.var rfl) rfl
  · exact .binary (.var rfl) .word rfl

private theorem unsigned_beq (width : TypeSystem.IntegerWidth) (word : Word) :
    (word == word.bitAnd (Word.ofNatModulo (2 ^ width.bits - 1))) = decide (word.val < 2 ^ width.bits) := by
  have bits := width.bits_le
  have positive := Nat.two_pow_pos width.bits
  have bounded : 2 ^ width.bits ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) bits
  have mask : (Word.ofNatModulo (2 ^ width.bits - 1)).val = 2 ^ width.bits - 1 :=
    Nat.mod_eq_of_lt (by show 2 ^ width.bits - 1 < 2 ^ 256; omega)
  have anded : (word.bitAnd (Word.ofNatModulo (2 ^ width.bits - 1))).val = word.val % 2 ^ width.bits := by
    show (word &&& Word.ofNatModulo (2 ^ width.bits - 1)).val = _
    rw [Fin.and_val, mask, Nat.and_two_pow_sub_one_eq_mod]
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_iff, Fin.ext_iff, anded]
  constructor
  · intro same
    rw [same]
    exact Nat.mod_lt _ positive
  · intro below
    exact (Nat.mod_eq_of_lt below).symm

private theorem signExtend_val {index : Word} (word : Word) (small : index.val < 32) :
    (index.signExtend word).val =
      if word.val % 2 ^ (8 * (index.val + 1)) < 2 ^ (8 * (index.val + 1) - 1) then
        word.val % 2 ^ (8 * (index.val + 1)) % 2 ^ 256
      else (2 ^ 256 - 2 ^ (8 * (index.val + 1)) + word.val % 2 ^ (8 * (index.val + 1))) % 2 ^ 256 := by
  unfold Word.signExtend
  rw [if_pos small]
  exact apply_ite Fin.val _ _ _

set_option linter.unusedSimpArgs false in
private theorem signed_beq (width : TypeSystem.IntegerWidth) (word : Word) :
    (word == (Word.ofNatModulo (width.bits / 8 - 1)).signExtend word) =
      (decide (word.val < 2 ^ (width.bits - 1)) || decide (2 ^ 256 - 2 ^ (width.bits - 1) ≤ word.val)) := by
  have bound : word.val < 2 ^ 256 := word.isLt
  have small : (Word.ofNatModulo (width.bits / 8 - 1)).val < 32 := by cases width <;> decide
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, Fin.ext_iff, Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff, signExtend_val word small]
  by_cases low : word.val % 2 ^ (8 * ((Word.ofNatModulo (width.bits / 8 - 1)).val + 1)) <
      2 ^ (8 * ((Word.ofNatModulo (width.bits / 8 - 1)).val + 1) - 1)
  · rw [if_pos low]
    cases width <;>
      simp only [TypeSystem.IntegerWidth.bits, Word.ofNatModulo, wordModulus, Nat.reduceDiv, Nat.reduceSub,
        Nat.reduceMod, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] at low ⊢ <;>
      constructor <;> intro h <;> omega
  · rw [if_neg low]
    cases width <;>
      simp only [TypeSystem.IntegerWidth.bits, Word.ofNatModulo, wordModulus, Nat.reduceDiv, Nat.reduceSub,
        Nat.reduceMod, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] at low ⊢ <;>
      constructor <;> intro h <;> omega

/-- A word equals its canonical form exactly when it is canonical. -/
theorem canonicalWord_beq (type : TypeSystem.FixedInteger) (word : Word) :
    (word == canonicalWord type word) = type.canonical word.val := by
  obtain ⟨signed, width⟩ := type
  cases signed
  · simp only [canonicalWord, TypeSystem.FixedInteger.canonical, Bool.false_eq_true, ↓reduceIte]
    exact unsigned_beq width word
  · simp only [canonicalWord, TypeSystem.FixedInteger.canonical, ↓reduceIte]
    exact signed_beq width word

/-- Every word is canonical at the 256-bit width. -/
theorem canonical_w256 {type : TypeSystem.FixedInteger} (wide : type.width = .w256) (word : Word) :
    type.canonical word.val = true := by
  obtain ⟨signed, width⟩ := type
  cases wide
  have bound : word.val < 2 ^ 256 := word.isLt
  cases signed
  · show decide (word.val < 2 ^ 256) = true
    exact decide_eq_true bound
  · show (decide (word.val < 2 ^ 255) || decide (2 ^ 256 - 2 ^ 255 ≤ word.val)) = true
    have half : (2 : Nat) ^ 256 - 2 ^ 255 = 2 ^ 255 := by decide
    rw [Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff, half]
    omega

private theorem condition {type : TypeSystem.FixedInteger} {environment : Environment} {store : Store}
    (word : Word) :
    Evaluates (.word word :: environment) store
      (.binary .wordEq (.var 0) (SourceCoreInteger.canonicalForm type (.var 0)))
      (.bool (type.canonical word.val)) store := by
  have evaluated : Evaluates (.word word :: environment) store
      (.binary .wordEq (.var 0) (SourceCoreInteger.canonicalForm type (.var 0)))
      (.bool (word == canonicalWord type word)) store :=
    .binary (.var rfl) (canonicalForm_evaluates type word) rfl
  rwa [canonicalWord_beq] at evaluated

/-- A canonical word passes the check. -/
theorem check_success {type : TypeSystem.FixedInteger} {environment : Environment} {store : Store} {word : Word}
    (canonical : type.canonical word.val = true) :
    Evaluates (.word word :: environment) store (SourceCoreInteger.conversionCheck type)
      (.inRight .word (.word word)) store := by
  have test := condition (type := type) (environment := environment) (store := store) word
  rw [canonical] at test
  exact .ifTrue test (.inRight (.var rfl))

/-- A word that is not canonical fails the check with the dirty-integer reason. -/
theorem check_failure {type : TypeSystem.FixedInteger} {environment : Environment} {store : Store} {word : Word}
    (dirty : type.canonical word.val = false) :
    Evaluates (.word word :: environment) store (SourceCoreInteger.conversionCheck type)
      (.inLeft .word (.word SourceCorePanics.dirtyReason)) store := by
  have test := condition (type := type) (environment := environment) (store := store) word
  rw [dirty] at test
  exact .ifFalse test (.inLeft .word)

theorem conversion_success {type : TypeSystem.FixedInteger} {environment : Environment} {before after : Store}
    {argument : Expr} {word : Word}
    (evaluation : Evaluates environment before argument (.inRight .word (.word word)) after)
    (canonical : type.canonical word.val = true) :
    Evaluates environment before (SourceCoreInteger.conversion type argument) (.inRight .word (.word word)) after := by
  unfold SourceCoreInteger.conversion
  split
  · exact evaluation
  · exact LanguageResult.bind_success _ evaluation (check_success canonical)

theorem conversion_dirty {type : TypeSystem.FixedInteger} {environment : Environment} {before after : Store}
    {argument : Expr} {word : Word}
    (evaluation : Evaluates environment before argument (.inRight .word (.word word)) after)
    (dirty : type.canonical word.val = false) :
    Evaluates environment before (SourceCoreInteger.conversion type argument)
      (.inLeft .word (.word SourceCorePanics.dirtyReason)) after := by
  have narrow : type.width ≠ .w256 := fun wide => by simp [canonical_w256 wide word] at dirty
  unfold SourceCoreInteger.conversion
  rw [if_neg narrow]
  exact LanguageResult.bind_success _ evaluation (check_failure dirty)

theorem conversion_failure {type : TypeSystem.FixedInteger} {environment : Environment} {before after : Store}
    {argument : Expr} {reason : Word}
    (evaluation : Evaluates environment before argument (.inLeft .word (.word reason)) after) :
    Evaluates environment before (SourceCoreInteger.conversion type argument) (.inLeft .word (.word reason)) after := by
  unfold SourceCoreInteger.conversion
  split
  · exact evaluation
  · exact LanguageResult.bind_failure _ evaluation

/-- A builtin conversion is `conversion` at a fixed-width type and the
argument itself otherwise. -/
theorem builtinConversion_cases (target : TypeSystem.Ty) :
    (∃ type, ∀ argument, SourceCoreInteger.builtinConversion target argument =
      SourceCoreInteger.conversion type argument) ∨
    (∀ argument, SourceCoreInteger.builtinConversion target argument = argument) := by
  by_cases fixed : ∃ type, target = .fixed type
  · obtain ⟨type, rfl⟩ := fixed
    exact .inl ⟨type, fun _ => rfl⟩
  · refine .inr fun argument => ?_
    unfold SourceCoreInteger.builtinConversion
    split
    · rename_i type
      exact absurd ⟨type, rfl⟩ fixed
    · rfl

/-- A failing argument fails every conversion with its own reason. -/
theorem builtinConversion_failure {target : TypeSystem.Ty} {environment : Environment} {before after : Store}
    {argument : Expr} {reason : Word}
    (evaluation : Evaluates environment before argument (.inLeft .word (.word reason)) after) :
    Evaluates environment before (SourceCoreInteger.builtinConversion target argument)
      (.inLeft .word (.word reason)) after := by
  rcases builtinConversion_cases target with ⟨type, same⟩ | same
  · rw [same]
    exact conversion_failure evaluation
  · rw [same]
    exact evaluation

/-- The argument of a measured conversion runs within its grade. -/
theorem argument_of_conversion {target : TypeSystem.Ty} {size : Nat} {environment : Environment}
    {before after : Store} {argument : Expr} {value : Value}
    (evaluation : EvaluationSize size environment before (SourceCoreInteger.builtinConversion target argument)
      value after) :
    ∃ argumentSize argumentValue middle, argumentSize ≤ size ∧
      EvaluationSize argumentSize environment before argument argumentValue middle := by
  rcases builtinConversion_cases target with ⟨type, same⟩ | same
  · rw [same] at evaluation
    unfold SourceCoreInteger.conversion at evaluation
    split at evaluation
    · exact ⟨size, value, after, Nat.le_refl _, evaluation⟩
    · unfold LanguageResult.bind at evaluation
      cases evaluation with
      | caseLeft scrutinee _ => exact ⟨_, _, _, by omega, scrutinee⟩
      | caseRight scrutinee _ => exact ⟨_, _, _, by omega, scrutinee⟩
  · rw [same] at evaluation
    exact ⟨size, value, after, Nat.le_refl _, evaluation⟩

theorem builtinConversion_rename (target : TypeSystem.Ty) (argument : Expr) (ξ : Renaming) :
    (SourceCoreInteger.builtinConversion target argument).rename ξ =
      SourceCoreInteger.builtinConversion target (argument.rename ξ) := by
  rcases builtinConversion_cases target with ⟨type, same⟩ | same
  · rw [same, same]
    obtain ⟨signed, width⟩ := type
    by_cases wide : width = .w256
    · simp only [SourceCoreInteger.conversion, wide, ↓reduceIte]
    · simp only [SourceCoreInteger.conversion, wide, ↓reduceIte]
      cases signed <;> rfl
  · rw [same, same]

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedConversionCode
end

section
/-! Builtin conversions of named-row bodies as compiler sites. A conversion
site has no coercions or requirements, is not a generalized initializer and
lies in a row without evidence assumptions, so the named policy's special
callback declines it and its read policy is the compatible reader, as at a
direct site. Its builtin converts a word (`word`): `uintN(w)`, `intN(w)`, and
`Typedef.abs` and `Typedef.rep` at `word`. The compiler lowers a conversion
where it is called (`of_accepted`): its argument at `word`, and the conversion
of the argument's code. The callee of a conversion is a builtin reference that
the compiler cannot lower on its own (`reference_rejected`), since a conversion
is no closure of the builtin inventory. `conversionSite?` and
`conversionReference?` recognize both on an actually compiled row. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedConversionSites
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context representation)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)

/-- A conversion of a word in a named-row body. -/
structure ConversionSite {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id callee argument : ExpressionId) (function : BuiltinFunctionId)
    (target : TypeSystem.Ty) where
  node : ExpressionNode
  found : source.lookupExpression? id = some node
  form : node.form = .call callee [argument] (.builtinFunction function)
  coercions : node.coercions = []
  requirements : node.requirements = []
  notInitializer : prepared.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none
  assumptions : named.specialized.assumptions = []
  conversion : function.conversion? = some target
  word : function.parameterTypes = [.word]

/-- The callee of a conversion: a reference to a conversion builtin, in a row
without evidence assumptions. -/
structure ConversionReference {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) where
  node : ExpressionNode
  name : String
  function : BuiltinFunctionId
  target : TypeSystem.Ty
  found : source.lookupExpression? id = some node
  form : node.form = .reference name (.builtinFunction function)
  coercions : node.coercions = []
  requirements : node.requirements = []
  notInitializer : prepared.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none
  assumptions : named.specialized.assumptions = []
  conversion : function.conversion? = some target

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {id callee argument : ExpressionId}
  {function : BuiltinFunctionId} {target : TypeSystem.Ty}

theorem contextual (site : ConversionSite prepared named source id callee argument function target) :
    SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      (context prepared named).plan prepared.base.locals named.signature.key none source id = .ok source := by
  simp [SourceCoreGeneralFunctions.contextualSource, site.found, site.form]

theorem reference_contextual (reference : ConversionReference prepared named source id) :
    SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      (context prepared named).plan prepared.base.locals named.signature.key none source id = .ok source := by
  simp [SourceCoreGeneralFunctions.contextualSource, reference.found, reference.form]

private theorem ordinary_nil {node : ExpressionNode} (requirements : node.requirements = [])
    (coercions : node.coercions = []) : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
  unfold SourceCompilationPlan.ordinaryOwnedRequirements?
  rw [requirements, coercions]
  rfl

private theorem evidence_none (site : ConversionSite prepared named source id callee argument function target)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none := by
  simp [SourceCoreEvidence.lowerWithProjector, ordinary_nil site.requirements site.coercions, site.found,
    site.form, site.requirements, site.coercions, site.assumptions]

private theorem reference_evidence (reference : ConversionReference prepared named source id)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none := by
  simp [SourceCoreEvidence.lowerWithProjector, ordinary_nil reference.requirements reference.coercions,
    reference.found, reference.form, reference.requirements, reference.coercions, reference.assumptions]

variable {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : Compilation prepared named diagnostics code)

/-- The named policy's special callback declines a conversion site. -/
theorem special (site : ConversionSite prepared named source id callee argument function target) (rootFuel : Nat)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok none := by
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  have ownerEq : (context prepared named).owner = named.signature.key := rfl
  simp only [ownerEq, contextual site, bind, Except.bind, pure, Except.pure, site.found,
    site.notInitializer, Option.filter_none]
  rw [evidence_none site child budget scope reasonAt]
  simp [site.form]

/-- The named policy's special callback declines a conversion's callee. -/
theorem reference_special (reference : ConversionReference prepared named source id) (rootFuel : Nat)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok none := by
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  have ownerEq : (context prepared named).owner = named.signature.key := rfl
  simp only [ownerEq, reference_contextual reference, bind, Except.bind, pure, Except.pure, reference.found,
    reference.notInitializer, Option.filter_none]
  rw [reference_evidence reference child budget scope reasonAt]
  simp [reference.form]

theorem read (site : ConversionSite prepared named source id callee argument function target) (rootFuel : Nat) :
    (namedPolicy compiled rootFuel).readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  simp only [namedPolicy, contextual site, bind, Except.bind]
  rfl

theorem reference_read (reference : ConversionReference prepared named source id) (rootFuel : Nat) :
    (namedPolicy compiled rootFuel).readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  simp only [namedPolicy, reference_contextual reference, bind, Except.bind]
  rfl

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty} {done : Unit}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok done) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

/-- The compiler's conversion branch at a read node: the argument at `word`,
and the conversion of the argument's code at `word`. -/
theorem lowered_of_accepted
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee argument : ExpressionId}
    {function : BuiltinFunctionId} {target : TypeSystem.Ty} {node : ExpressionNode} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .call callee [argument] (.builtinFunction function))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (conversion : function.conversion? = some target)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    ∃ argumentCode,
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope argument
        reasonAt = .ok ⟨.word, argumentCode⟩ ∧
      type = .word ∧ lowered = ⟨.word, SourceCoreInteger.builtinConversion target argumentCode⟩ := by
  cases hook : policy.lowerSpecial? <;> simp only [hook] at special
  all_goals
    unfold SourceCoreFunctions.lowerExpressionWithPolicy at accepted
    simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, hook, special, form, read, conversion,
      bind, Except.bind, pure, Except.pure] at accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨codes, generated, accepted⟩ := bind_ok accepted
    cases child : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope
        argument reasonAt with
    | error reason => simp [List.mapM_cons, child, bind, Except.bind] at generated
    | ok argumentLowered =>
      simp only [List.mapM_cons, List.mapM_nil, child, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at generated
      subst codes
      dsimp only at accepted
      obtain ⟨_, argumentChecked, accepted⟩ := bind_ok accepted
      obtain ⟨_, resultChecked, accepted⟩ := bind_ok accepted
      have argumentType := ensureType_ok argumentChecked
      have resultType := ensureType_ok resultChecked
      obtain ⟨argumentType', argumentCode⟩ := argumentLowered
      dsimp only at argumentType
      subst argumentType resultType
      cases accepted
      exact ⟨argumentCode, rfl, rfl, rfl⟩

/-- An accepted conversion lowers its argument at `word` and emits the
conversion of the argument's code, at `word`. -/
theorem of_accepted
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee argument : ExpressionId}
    {function : BuiltinFunctionId} {target : TypeSystem.Ty}
    {node : ExpressionNode} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee [argument] (.builtinFunction function))
    (conversion : function.conversion? = some target)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    ∃ argumentCode,
      CompatibleExpressionReads.Metadata values.checked source id node .word ∧
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope argument
        reasonAt = .ok ⟨.word, argumentCode⟩ ∧
      lowered = ⟨.word, SourceCoreInteger.builtinConversion target argumentCode⟩ := by
  have original := accepted
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
        compilation childSource childScope childId childReasonAt) (fuel + 1)
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      simp only [form] at accepted
      obtain ⟨pair, read, _remaining⟩ := bind_ok accepted
      rcases pair with ⟨other, type⟩
      have metadata := CompatibleExpressionReads.metadata_of_read (readPolicy.symm ▸ read)
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst other
      obtain ⟨argumentCode, generated, rfl, emitted⟩ :=
        lowered_of_accepted owner found read form (special _ _) conversion original
      exact ⟨argumentCode, metadata, generated, emitted⟩
  · simp [owner, bind, Except.bind] at accepted

/-- The named compiler cannot lower a conversion's callee on its own: a
conversion is no closure of the builtin inventory. -/
theorem reference_rejected (reference : ConversionReference prepared named source id) (rootFuel : Nat)
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr} :
    SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy compiled rootFuel) (namedLowerBody compiled) fuel
      (context prepared named) source scope id reasonAt ≠ .ok lowered := by
  intro accepted
  cases fuel with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel =>
    have special : ∀ child budget, (match (namedPolicy compiled rootFuel).lowerSpecial? with
        | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
        | some lower => lower (context prepared named) child budget source scope id reasonAt) = .ok none :=
      fun child budget => reference_special compiled reference rootFuel child budget scope reasonAt
    rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    by_cases owner : id.occurrence.owner = source.owner
    · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, reference.found, bind, Except.bind, pure,
        Except.pure] at accepted
      have bypass := special (fun budget childSource childScope childId childReasonAt =>
        SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy compiled rootFuel) (namedLowerBody compiled)
          (min budget fuel) (context prepared named) childSource childScope childId childReasonAt) (fuel + 1)
      cases hook : (namedPolicy compiled rootFuel).lowerSpecial? <;> simp only [hook] at accepted bypass
      all_goals try rw [bypass] at accepted
      all_goals
        simp only [reference.form] at accepted
        obtain ⟨pair, read, accepted⟩ := bind_ok accepted
        rcases pair with ⟨other, type⟩
        have metadata := CompatibleExpressionReads.metadata_of_read
          ((reference_read compiled reference rootFuel).symm ▸ read)
        have same := Option.some.inj (metadata.found.symm.trans reference.found)
        subst other
        simp only [reference.form] at accepted
        obtain ⟨_, referenced, _⟩ := bind_ok accepted
        cases BuiltinCalls.reference_of_accepted referenced with
        | intro _ _ inventory _ _ =>
          have closure := BuiltinFunctionId.conversion?_of_inventory inventory
          rw [reference.conversion] at closure
          cases closure
    · simp [owner, bind, Except.bind] at accepted

/-- Proof-producing recognition of a conversion site of the row. -/
def conversionSite? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) :
    Option (Σ' (callee argument : ExpressionId) (function : BuiltinFunctionId) (target : TypeSystem.Ty),
      ConversionSite prepared named source id callee argument function target) :=
  match found : source.lookupExpression? id with
  | none => none
  | some node =>
    match form : node.form with
    | .call callee [argument] (.builtinFunction function) =>
      match conversion : function.conversion? with
      | none => none
      | some target =>
        if word : function.parameterTypes = [.word] then
          match coercions : node.coercions, requirements : node.requirements with
          | [], [] =>
            match initializer : prepared.base.locals.bindings.find? (fun binding =>
                decide (binding.caller = named.signature.key ∧ binding.initializer = id)) with
            | some _ => none
            | none =>
              match assumptions : named.specialized.assumptions with
              | [] => some ⟨callee, argument, function, target,
                  ⟨node, found, form, coercions, requirements, initializer, assumptions, conversion, word⟩⟩
              | _ :: _ => none
          | _, _ => none
        else none
    | _ => none

/-- Proof-producing recognition of a conversion's callee. -/
def conversionReference? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) : Option (ConversionReference prepared named source id) :=
  match found : source.lookupExpression? id with
  | none => none
  | some node =>
    match form : node.form with
    | .reference name (.builtinFunction function) =>
      match conversion : function.conversion? with
      | none => none
      | some target =>
        match coercions : node.coercions, requirements : node.requirements with
        | [], [] =>
          match initializer : prepared.base.locals.bindings.find? (fun binding =>
              decide (binding.caller = named.signature.key ∧ binding.initializer = id)) with
          | some _ => none
          | none =>
            match assumptions : named.specialized.assumptions with
            | [] => some ⟨node, name, function, target, found, form, coercions, requirements, initializer,
                assumptions, conversion⟩
            | _ :: _ => none
        | _, _ => none
    | _ => none

/-- A conversion site depends on its row only through the row's key and its
empty assumptions. -/
def transport {first second : SourceCoreGeneralFunctions.Function}
    (keyEq : first.signature.key = second.signature.key) (assumptions : second.specialized.assumptions = [])
    (site : ConversionSite prepared first source id callee argument function target) :
    ConversionSite prepared second source id callee argument function target where
  node := site.node
  found := site.found
  form := site.form
  coercions := site.coercions
  requirements := site.requirements
  notInitializer := keyEq ▸ site.notInitializer
  assumptions := assumptions
  conversion := site.conversion
  word := site.word

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedConversionSites
end

section
/-! The token law of a dirty word. A conversion of a word that is not
canonical for its type fails with `SourceCorePanics.dirtyReason`, which a public
diagnostic table without reasons in the reserved range decodes as
`DirtyHigherBitsForInteger()`. As with `RecursiveStageMeaning.FaultTokens`,
theorems over a fault relation take the law as an instance argument, and
`dirtyToken` gives it for the decoded staged faults of such a table. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedConversionFaults
open Core Frontend

/-- A dirty word's failure is represented by the dirty-integer reason. -/
class DirtyToken (faults : RecursiveStageMeaning.FaultRep) : Prop where
  dirty : faults (.semantic .dirtyHigherBitsForInteger) SourceCorePanics.dirtyReason

theorem dirtyToken {table : SourceCoreFaultSites.Table} (free : table.PanicFree) :
    DirtyToken (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults table) :=
  ⟨CallableIndexedOwnedPublicDecodedCallFaults.dirty free⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedConversionFaults
end

section
/-! The cell-aware head of a conversion. A conversion runs its argument in the
same invocation and applies its builtin at the reached heap and store, which
the application keeps. The native check returns a canonical word and fails with
the dirty-integer reason on any other word, which `DirtyToken` represents; an
argument's failure is the conversion's own. Preservation uses the argument's
meaning below the grade. Reflection uses it at most at the grade, since at
`word` and at the 256-bit types the conversion is its argument's code. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedConversions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds
open CallableIndexedOwnedPreparedStagedPhysicalDirectHeadBounds (Point)
open CellAwareInvocationAcceptedConversionCode
open CellAwareInvocationAcceptedConversionFaults (DirtyToken)
universe u

/-- The static facts of a conversion node that its head reads. -/
structure Node (source : TypedSource) (id callee argument : ExpressionId) (node : ExpressionNode)
    (function : BuiltinFunctionId) (target : TypeSystem.Ty) : Prop where
  found : source.lookupExpression? id = some node
  form : node.form = .call callee [argument] (.builtinFunction function)
  coercions : node.coercions = []
  requirements : node.requirements = []
  conversion : function.conversion? = some target
  word : function.parameterTypes = [.word]
  argumentFound : ∃ argumentNode, source.lookupExpression? argument = some argumentNode

/-- The Source application of a conversion of a word. -/
inductive Applied : BuiltinFunctionId → TypeSystem.Ty → Word → Staging.Recursive.Outcome → Prop where
  | canonical {type : TypeSystem.FixedInteger} {word : Word} (canonical : type.canonical word.val = true) :
      Applied (.fixedFromWord type) (.fixed type) word (.value (.word word))
  | dirty {type : TypeSystem.FixedInteger} {word : Word} (dirty : type.canonical word.val = false) :
      Applied (.fixedFromWord type) (.fixed type) word (.fault (.semantic .dirtyHigherBitsForInteger))
  | identity {word : Word} : Applied .wordIdentity .word word (.value (.word word))

variable {function : BuiltinFunctionId} {target : TypeSystem.Ty}

/-- Every original rule of a conversion's application at a word is inspected:
the word's runtime type is its parameter type, so arity and type faults are
excluded, and the application keeps the heap. -/
theorem applied {program : Program} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {size : Nat} {heap after : Dynamic.Heap} {word : Word}
    {outcome : Staging.Recursive.Outcome}
    (conversion : function.conversion? = some target) (parameter : function.parameterTypes = [.word])
    (called : Staging.Recursive.Size.Applies program stages size invocation context heap (.builtin ⟨function⟩)
      [.word word] outcome after) :
    after = heap ∧ Applied function target word outcome := by
  cases called with
  | builtin primitive =>
    refine ⟨rfl, ?_⟩
    cases primitive with
    | fixedFromWord canonical =>
      simp only [BuiltinFunctionId.conversion?, Option.some.injEq] at conversion
      subst conversion
      exact .canonical canonical
    | wordIdentity =>
      simp only [BuiltinFunctionId.conversion?, Option.some.injEq] at conversion
      subst conversion
      exact .identity
    | fixedToWord _ =>
      exact absurd parameter (by simp [BuiltinFunctionId.parameterTypes, TypeSystem.Ty.fixed, TypeSystem.Ty.word])
    | wordToInteger => simp [BuiltinFunctionId.conversion?] at conversion
  | builtinArity mismatch => simp [parameter] at mismatch
  | builtinType _ mismatch =>
    exfalso
    change Dynamic.ValuesFirstTypeMismatch [.word word] function.parameterTypes _ _ at mismatch
    rw [parameter] at mismatch
    cases mismatch with
    | head actual different => cases actual; exact different rfl
    | tail _ rest => cases rest
  | builtinFault fault =>
    refine ⟨rfl, ?_⟩
    cases fault with
    | fixedFromWord dirty =>
      simp only [BuiltinFunctionId.conversion?, Option.some.injEq] at conversion
      subst conversion
      exact .dirty dirty

/-- A conversion of a word applies in the Source. -/
theorem applies (conversion : function.conversion? = some target) (parameter : function.parameterTypes = [.word])
    (word : Word) : ∃ outcome, Applied function target word outcome := by
  cases function <;>
    simp [BuiltinFunctionId.conversion?, BuiltinFunctionId.parameterTypes, TypeSystem.Ty.fixed, TypeSystem.Ty.word]
      at conversion parameter
  case fixedFromWord type =>
    subst conversion
    cases canonical : type.canonical word.val
    · exact ⟨_, .dirty canonical⟩
    · exact ⟨_, .canonical canonical⟩
  case wordIdentity =>
    subst conversion
    exact ⟨_, .identity⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {registry : SourceCoreRawMetadata.Registry} {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {scope : SourceCoreLocalCell.Scope} {id callee argument : ExpressionId} {node : ExpressionNode}
  {argumentCode : Expr}
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

private theorem argument_typed (unique : NodeOccurrencesUnique invocation.source)
    (site : Node invocation.source id callee argument node function target)
    (typed : ExpressionHasType invocation.source context id node.type) :
    ∃ argumentNode, invocation.source.lookupExpression? argument = some argumentNode ∧
      ExpressionHasType invocation.source context argument argumentNode.type ∧
      node.type = function.returnType := by
  obtain ⟨argumentsTyped, resultType⟩ :=
    CallableIndexedOwnedPreparedStagedBuiltinSourceInversion.source_types unique site.found site.form
      site.coercions typed
  obtain ⟨argumentNode, argumentFound⟩ := site.argumentFound
  exact ⟨argumentNode, argumentFound, CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed
    unique argumentsTyped (List.mem_singleton_self _) argumentFound, resultType⟩

/-- A Source trace of a conversion determines the actual native check and the
argument's reached state. -/
theorem preserves [RecursiveStageMeaning.FaultTokens faults] [DirtyToken faults]
    (site : Node invocation.source id callee argument node function target)
    (unique : NodeOccurrencesUnique invocation.source)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program stages)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context) (size : Nat)
    (childMeaning : PreservesBelow (attachment := attachment) bridge context model index stages invocation
      (Point scope argument ⟨.word, argumentCode⟩) faults size) :
    PreservesAt (attachment := attachment) bridge context model index stages invocation
      (Point scope id ⟨.word, SourceCoreInteger.builtinConversion target argumentCode⟩) faults size := by
  intro current expression code certified actualNode found sourceTyped mapping world administrative environment
    canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped
    initial admitted authority physical owner ownerFrame trace
  obtain ⟨currentEq, expressionEq, codeEq⟩ := certified
  subst current expression code
  cases Option.some.inj (found.symm.trans site.found)
  obtain ⟨argumentNode, argumentFound, argumentTyped, resultType⟩ := argument_typed unique site sourceTyped
  have raw : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreInteger.builtinConversion target argumentCode).rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type .word faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    rw [builtinConversion_rename]
    rcases CallableIndexedOwnedPreparedStagedBuiltinSourceInversion.children unique site.found site.form trace with
      ⟨sequenceSize, invocationSize, argumentsHeap, values, sizeEq, sequence, called⟩ |
      ⟨sequenceSize, failure, sizeEq, outcomeEq, sequence⟩
    · cases sequence with
      | cons head tail =>
        cases tail
        obtain ⟨argumentValue, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
            frame, heapMetadata, effect, reached, related, _post⟩ :=
          childMeaning _ (by
              simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at sizeEq
              omega) ⟨rfl, rfl, rfl⟩ argumentFound argumentTyped environments heaps locals agrees actualTyped
            initial admitted authority physical owner ownerFrame head
        cases represented with
        | value payload =>
          obtain ⟨word, rfl, rfl⟩ := CompatibleExpressionPrimitives.word_fields payload
          obtain ⟨rfl, result⟩ := applied site.conversion site.word called
          rw [resultType]
          cases result with
          | canonical canonical =>
            exact ⟨_, finalStore, finalMap, finalWorld, conversion_success evaluated canonical,
              .value (ValueRep.fixed word canonical), finalHeaps, maps, worlds, frame, heapMetadata, effect, reached,
              related⟩
          | dirty dirty =>
            exact ⟨_, finalStore, finalMap, finalWorld, conversion_dirty evaluated dirty,
              .fault DirtyToken.dirty, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
          | identity =>
            exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .value (ValueRep.word word), finalHeaps, maps, worlds,
              frame, heapMetadata, effect, reached, related⟩
    · subst outcomeEq
      cases sequence with
      | headFault head =>
        obtain ⟨argumentValue, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
            frame, heapMetadata, effect, reached, related, _post⟩ :=
          childMeaning _ (by
              simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at sizeEq
              omega) ⟨rfl, rfl, rfl⟩ argumentFound argumentTyped environments heaps locals agrees actualTyped
            initial admitted authority physical owner ownerFrame head
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, builtinConversion_failure evaluated, .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
      | tailFault _ tail => cases tail
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, effect, reached, related⟩ := raw
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers
      locals sourceTyped trace frame⟩

/-- Native completion of a conversion reconstructs its staged Source
execution: the argument's, and the application of the builtin. -/
theorem reflects [RecursiveStageMeaning.FaultTokens faults] [DirtyToken faults]
    (site : Node invocation.source id callee argument node function target)
    (unique : NodeOccurrencesUnique invocation.source)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program stages)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context) (size : Nat)
    (childMeaning : ReflectsBelow (attachment := attachment) bridge context model index stages invocation
      (Point scope argument ⟨.word, argumentCode⟩) faults (size + 1)) :
    ReflectsAt (attachment := attachment) bridge context model index stages invocation
      (Point scope id ⟨.word, SourceCoreInteger.builtinConversion target argumentCode⟩) faults size := by
  intro current expression code certified actualNode found sourceTyped mapping world administrative environment
    canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped
    initial admitted authority physical owner ownerFrame completed
  obtain ⟨currentEq, expressionEq, codeEq⟩ := certified
  subst current expression code
  cases Option.some.inj (found.symm.trans site.found)
  obtain ⟨argumentNode, argumentFound, argumentTyped, resultType⟩ := argument_typed unique site sourceTyped
  have occurrence : Staging.Recursive.Occurrence invocation id
      (.call callee [argument] (.builtinFunction function)) :=
    ⟨_, lookupExpression?_sound site.found, site.form, site.requirements, site.coercions⟩
  have raw : ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before id
        outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type .word faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    change EvaluationSize size actual store ((SourceCoreInteger.builtinConversion target argumentCode).rename ξ)
      value finalStore at completed
    rw [builtinConversion_rename] at completed
    have complete := completed.sound
    obtain ⟨argumentSize, argumentValue, middle, within, argumentEvaluation⟩ := argument_of_conversion completed
    obtain ⟨_, argumentOutcome, after, finalMap, finalWorld, argumentTrace, represented, finalHeaps, maps, worlds,
        frame, heapMetadata, effect, reached, related, _post⟩ :=
      childMeaning argumentSize (Nat.lt_succ_of_le within) ⟨rfl, rfl, rfl⟩ argumentFound argumentTyped
        environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame
        argumentEvaluation
    cases represented with
    | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic (builtinConversion_failure argumentEvaluation.sound) complete
      exact ⟨_, _, after, finalMap, finalWorld, .builtinArgumentsFault occurrence (.headFault argumentTrace),
        .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
    | value payload =>
      obtain ⟨word, rfl, rfl⟩ := CompatibleExpressionPrimitives.word_fields payload
      rw [resultType]
      obtain ⟨_, result⟩ := applies site.conversion site.word word
      cases result with
      | canonical canonical =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic (conversion_success argumentEvaluation.sound canonical)
          complete
        exact ⟨_, _, after, finalMap, finalWorld,
          .builtinApplied occurrence (.cons argumentTrace .nil) (.builtin (.fixedFromWord canonical)),
          .value (ValueRep.fixed word canonical), finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
      | dirty dirty =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic (conversion_dirty argumentEvaluation.sound dirty) complete
        exact ⟨_, _, after, finalMap, finalWorld,
          .builtinApplied occurrence (.cons argumentTrace .nil) (.builtinFault (.fixedFromWord dirty)),
          .fault DirtyToken.dirty, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
      | identity =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic argumentEvaluation.sound complete
        exact ⟨_, _, after, finalMap, finalWorld,
          .builtinApplied occurrence (.cons argumentTrace .nil) (.builtin (.wordIdentity word)),
          .value (ValueRep.word word), finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, effect, reached, related⟩ := raw
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers
      locals sourceTyped trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedConversions
end

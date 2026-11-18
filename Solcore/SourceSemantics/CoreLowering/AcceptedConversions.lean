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
  `CellAwareInvocationAcceptedConversionFaults.dirtyToken`, the token law of a dirty word.

`Typedef.rep` at a fixed-width type is no site. Its parameter type is the fixed-width type, while
a fixed-width value's runtime type is `word`, so the Source rule `builtinType` gives a type
mismatch where the native code returns the word.
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
is no closure of the builtin inventory. -/
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

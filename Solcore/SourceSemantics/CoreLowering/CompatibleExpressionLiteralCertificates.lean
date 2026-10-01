import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCertificates
import Solcore.SourceSemantics.CoreLowering.BasicExpressionCertificates

/-! Atomic literal certificates for the actual shared function compiler.
The numeric validators retain their original requirement identity and exact
Word or Integer target. A successful arbitrary override is outside this
ordinary branch; its explicit bypass receipt is required. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiterals
open Core Frontend SourceInference

/-- The ordinary atomic grammar. Unary minus is a separate expression node. -/
inductive Atomic : ExpressionForm → Prop where
  | unit : Atomic (.tuple [])
  | bool (name : String) (value : Bool) : Atomic (.reference name (.builtinBoolean value))
  | word (literal : Syntax.CoreLiteralValue) : Atomic (.literal literal)
  | integer (literal : Syntax.CoreLiteralValue) (resolution : IntegerLiteralResolution) :
      Atomic (.integerLiteral literal resolution)

/-- A literal certificate contains metadata and a numeric denotation only. -/
inductive Literal (solved : List SolvedRequirement) (node : ExpressionNode) :
    Core.Ty → Core.Expr → Prop where
  | unit (form : node.form = .tuple []) (type : node.type = .unit)
      (requirements : node.requirements = []) (coercions : node.coercions = []) :
      Literal solved node .unit (LanguageResult.success .unit)
  | bool {name : String} (value : Bool)
      (form : node.form = .reference name (.builtinBoolean value)) (type : node.type = .bool)
      (requirements : node.requirements = []) (coercions : node.coercions = []) :
      Literal solved node .bool (LanguageResult.success (.bool value))
  | word {literal : Syntax.CoreLiteralValue} (value : Word)
      (form : node.form = .literal literal) (type : node.type = .word)
      (requirements : node.requirements = []) (coercions : node.coercions = [])
      (meaning : WordLiteralDenotes ⟨node.span, literal⟩ value) :
      Literal solved node .word (LanguageResult.success (.word value))
  | resolvedWord {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
      {validated : SourceCoreElaboration.WordIntegerLiteral}
      (form : node.form = .integerLiteral literal resolution)
      (metadata : SourceCoreElaboration.WordIntegerLiteralCertificate solved node literal resolution validated) :
      Literal solved node .word (LanguageResult.success (.word validated.value))
  | resolvedInteger {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
      {validated : SourceCoreElaboration.NativeIntegerLiteral}
      (form : node.form = .integerLiteral literal resolution)
      (metadata : SourceCoreElaboration.NativeIntegerLiteralCertificate solved node literal resolution validated) :
      Literal solved node .integer (LanguageResult.success (.integer validated.value))

def Certificate (solved : List SolvedRequirement) (source : TypedSource)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  ∃ node, source.lookupExpression? id = some node ∧ Literal solved node lowered.type lowered.expression

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (checked : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at checked

private theorem type_unit {type : TypeSystem.Ty} (related : LocalCell.TypeRepresents type .unit) : type = .unit := by
  cases related; rfl
private theorem type_bool {type : TypeSystem.Ty} (related : LocalCell.TypeRepresents type .bool) : type = .bool := by
  cases related; rfl
private theorem type_word {type : TypeSystem.Ty} (related : LocalCell.TypeRepresents type .word) : type = .word := by
  cases related; rfl

private theorem basic_literal {fuel : Nat} {solved : List SolvedRequirement}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {node : ExpressionNode} {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node)
    (atomic : Atomic node.form)
    (accepted : SourceCoreBasic.lowerExpression fuel source scope id reason = .ok lowered) :
    Literal solved node lowered.type lowered.expression := by
  cases fuel with
  | zero => simp [SourceCoreBasic.lowerExpression] at accepted
  | succ fuel =>
    cases read : SourceCoreBasic.readExpression source id with
    | error error => simp [SourceCoreBasic.lowerExpression, read, bind, Except.bind] at accepted
    | ok pair =>
      obtain ⟨other, type⟩ := pair
      obtain ⟨otherFound, metadata⟩ := BasicExpressions.readExpression_certificate read
      have same := Option.some.inj (otherFound.symm.trans found)
      subst other
      simp only [SourceCoreBasic.lowerExpression, read, bind, Except.bind] at accepted
      generalize form : node.form = shape at atomic
      cases atomic with
      | unit =>
        rw [form] at accepted
        cases check : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit type with
        | error error => simp [check] at accepted
        | ok output =>
          cases output
          have eq := ensureType_ok check
          subst type
          simp only [check, pure, Except.pure, Except.ok.injEq] at accepted
          subst lowered
          exact .unit form (type_unit metadata.types) metadata.requirements metadata.coercions
      | bool name value =>
        rw [form] at accepted
        cases check : SourceCoreBasic.ensureType (.occurrence id.occurrence) .bool type with
        | error error => simp [check] at accepted
        | ok output =>
          cases output
          have eq := ensureType_ok check
          subst type
          simp only [check, pure, Except.pure, Except.ok.injEq] at accepted
          subst lowered
          exact .bool value form (type_bool metadata.types) metadata.requirements metadata.coercions
      | word literal =>
        rw [form] at accepted
        cases check : SourceCoreBasic.ensureType (.occurrence id.occurrence) .word type with
        | error error => simp [check] at accepted
        | ok output =>
          cases output
          have eq := ensureType_ok check
          subst type
          cases decoded : interpretWordLiteral? ⟨node.span, literal⟩ with
          | none => simp [check, decoded] at accepted
          | some value =>
            simp only [check, decoded, pure, Except.pure, Except.ok.injEq] at accepted
            subst lowered
            exact .word value form (type_word metadata.types) metadata.requirements metadata.coercions
              (interpretWordLiteral?_sound decoded)
      | integer literal resolution => simp [form] at accepted

private theorem leaf_literal {fuel : Nat} {solved : List SolvedRequirement}
    {values : SourceCoreCompatibleValues.Context} {child : SourceCoreFunctions.ExpressionLowerer}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node)
    (atomic : Atomic node.form) (unitType : node.form = .tuple [] → node.type = .unit)
    (accepted : SourceCoreCompatibleDataExpressions.leafLowerer values child fuel source scope id reasonAt = .ok lowered) :
    Literal solved node lowered.type lowered.expression := by
  unfold SourceCoreCompatibleDataExpressions.leafLowerer at accepted
  cases read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id with
  | error error => simp [read, bind, Except.bind] at accepted
  | ok pair =>
    obtain ⟨other, type⟩ := pair
    have metadata := CompatibleExpressionReads.metadata_of_read read
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst other
    simp only [read, bind, Except.bind] at accepted
    generalize form : node.form = shape at atomic
    cases atomic with
    | unit =>
      rw [form] at accepted
      dsimp only at accepted
      simp only [List.mapM, List.mapM.loop, pure, Except.pure, bind, Except.bind, SourceCoreCalls.packArguments] at accepted
      change (do
        SourceCoreBasic.ensureType (.occurrence id.occurrence) type .unit
        pure ({ type := type, expression := LanguageResult.success .unit } : SourceCoreBasic.LoweredExpr)) = .ok lowered at accepted
      cases checked : SourceCoreBasic.ensureType (.occurrence id.occurrence) type .unit with
      | error error => simp [checked, Functor.map, Except.map] at accepted
      | ok output =>
        cases output
        have same : type = .unit := by
          by_cases same : type = .unit
          · exact same
          · simp [SourceCoreBasic.ensureType, same] at checked
        subst type
        simp only [checked, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
        subst lowered
        exact .unit form (unitType form) metadata.requirements metadata.coercions
    | bool name value | word literal | integer literal resolution =>
      rw [form] at accepted
      exact basic_literal found (by rw [form]; constructor) accepted

/-- Actual function lowering supplies the ordinary atomic receipt. The unit
raw type is explicit because compatible native projection also erases staging.
No value or execution is supplied by the caller. -/
theorem of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {context : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node)
    (atomic : Atomic node.form) (unitType : node.form = .tuple [] → node.type = .unit)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower context child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Certificate context.solvedRequirements source id lowered := by
  cases fuel with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel =>
    rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    by_cases owner : id.occurrence.owner = source.owner
    · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found,
        bind, Except.bind, pure, Except.pure] at accepted
      have bypass := special (fun budget childSource childScope childId childReasonAt =>
        SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) context childSource childScope childId childReasonAt) (fuel + 1)
      cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
      all_goals
        try rw [bypass] at accepted
      all_goals
        generalize form : node.form = shape at atomic
        cases atomic with
        | integer literal resolution =>
          simp only [form] at accepted
          split at accepted
          · cases validated : SourceCoreElaboration.validateNativeIntegerLiteral context.solvedRequirements node literal resolution with
            | error error => simp [validated, Except.mapError, bind, Except.bind] at accepted
            | ok output =>
              simp only [validated, Except.mapError, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
              subst lowered
              exact ⟨node, found, .resolvedInteger form (SourceCoreElaboration.validateNativeIntegerLiteral_sound validated)⟩
          · cases validated : SourceCoreElaboration.validateWordIntegerLiteral context.solvedRequirements node literal resolution with
            | error error => simp [validated, Except.mapError, bind, Except.bind] at accepted
            | ok output =>
              simp only [validated, Except.mapError, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
              subst lowered
              exact ⟨node, found, .resolvedWord form (SourceCoreElaboration.validateWordIntegerLiteral_sound validated)⟩
        | unit | bool name value | word literal =>
          simp only [form, readPolicy] at accepted
          cases read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id with
          | error error => simp [read] at accepted
          | ok pair =>
            obtain ⟨other, type⟩ := pair
            have metadata := CompatibleExpressionReads.metadata_of_read read
            have same := Option.some.inj (metadata.found.symm.trans found)
            subst other
            simp only [read, bind, Except.bind, leafPolicy, form] at accepted
            exact ⟨node, found, leaf_literal found (by rw [form]; constructor) unitType accepted⟩
    · simp [owner, bind, Except.bind] at accepted

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiterals

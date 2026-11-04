import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Paths
import Solcore.Frontend.SourceCoreCompatibleDataExpressions
import Solcore.SourceSemantics.WellFormed
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.FunctionCalls
import Solcore.Frontend.SourceCoreGeneralFunctions
import Solcore.SourceSemantics.Dynamic.Fault
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MappingsAndEquality
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceKeys

/-!
# Compatible expressions: reads and literals

Reads and their completion, literals, leaves and fault policies, and product trees.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionInstantiationLaws
/-! Source instantiation laws are attached to stored, admitted occurrences.
Raw closedness covers every retained substitution row, including unused ones.
The laws preserve the full instantiation and the original source context. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionInstantiationLaws
open Frontend SourceInference CompatibleSourceInstantiationClosure

def ConstructorLaw (source : TypedSource) (context : Context) (admitted : ExpressionId → Prop) : Prop :=
  ∀ id node instantiation arguments, admitted id → source.lookupExpression? id = some node →
    node.form = .constructor instantiation arguments →
    DataConstructorInstantiation.Admissible context instantiation →
    DataConstructorInstantiation.Valid context instantiation

def DeclarationLaw (source : TypedSource) (context : Context) (admitted : ExpressionId → Prop) : Prop :=
  ∀ id node callee arguments instantiation, admitted id → source.lookupExpression? id = some node →
    node.form = .call callee arguments (.declaration instantiation) →
    DeclarationInstantiation.Admissible context instantiation →
    DeclarationInstantiation.Valid context instantiation

def ConstructorRanges (source : TypedSource) (admitted : ExpressionId → Prop) : Prop :=
  ∀ id node instantiation arguments, admitted id → source.lookupExpression? id = some node →
    node.form = .constructor instantiation arguments →
    ClosedParameterRange instantiation.parameterSubstitution

def DeclarationRanges (source : TypedSource) (admitted : ExpressionId → Prop) : Prop :=
  ∀ id node callee arguments instantiation, admitted id → source.lookupExpression? id = some node →
    node.form = .call callee arguments (.declaration instantiation) →
    ClosedParameterRange instantiation.parameterSubstitution

variable {source : TypedSource} {context : Context} {admitted restricted : ExpressionId → Prop}

theorem ConstructorLaw.restrict (law : ConstructorLaw source context admitted)
    (subset : ∀ id, restricted id → admitted id) : ConstructorLaw source context restricted := by
  intro id node instantiation arguments allowed found form valid
  exact law id node instantiation arguments (subset id allowed) found form valid

theorem ConstructorRanges.restrict (ranges : ConstructorRanges source admitted)
    (subset : ∀ id, restricted id → admitted id) : ConstructorRanges source restricted := by
  intro id node instantiation arguments allowed found form
  exact ranges id node instantiation arguments (subset id allowed) found form

/-- Compatibility with the former globally closed flexible scopes. -/
theorem ConstructorLaw.of_closed (lexical : context.typeVariables = [])
    (residual : context.residualTypeVariables = false) : ConstructorLaw source context admitted := by
  intro _ _ _ _ _ _ _ admissible
  exact admissible.toValid lexical residual

theorem DeclarationLaw.of_closed (lexical : context.typeVariables = [])
    (residual : context.residualTypeVariables = false) : DeclarationLaw source context admitted := by
  intro _ _ _ _ _ _ _ _ admissible
  exact admissible.toValid lexical residual

/-- Only the used occurrence's raw substitution supplies closure. No compiler
acceptance or native representation is substituted for these source facts. -/
theorem ConstructorLaw.of_ranges (lexical : context.typeVariables = [])
    (ranges : ConstructorRanges source admitted) : ConstructorLaw source context admitted := by
  intro id node instantiation arguments allowed found form admissible
  exact constructor_valid admissible lexical (ranges id node instantiation arguments allowed found form)

theorem DeclarationLaw.of_ranges (lexical : context.typeVariables = [])
    (ranges : DeclarationRanges source admitted) : DeclarationLaw source context admitted := by
  intro id node callee arguments instantiation allowed found form admissible
  exact declaration_valid admissible lexical (ranges id node callee arguments instantiation allowed found form)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionInstantiationLaws
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCertificates
/-! Static receipts for the actual compatible local-read compiler. Mapping
initialization retains the exact successful encoder and quote calls. No source
or Core execution premise occurs in these certificates. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
open Core Frontend SourceInference
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

structure Metadata (checked : SourceCoreCompatibleCatalog.Checked) (source : TypedSource)
    (id : ExpressionId) (node : ExpressionNode) (type : Core.Ty) : Prop where
  found : source.lookupExpression? id = some node
  owner : id.occurrence.owner = source.owner
  requirements : node.requirements = []
  coercions : node.coercions = []
  projected : checked.catalog.project node.type = .ok type

theorem projectType_of_accepted {checked : SourceCoreCompatibleCatalog.Checked}
    {site : SourceCoreElaboration.ErrorSite} {sourceType : TypeSystem.Ty} {type : Core.Ty}
    (accepted : SourceCoreCompatibleDataExpressions.projectType checked site sourceType = .ok type) :
    checked.catalog.project sourceType = .ok type := by
  unfold SourceCoreCompatibleDataExpressions.projectType SourceCoreCompatibleCatalog.Checked.project at accepted
  cases projected : checked.catalog.project sourceType with
  | error error => simp [projected, bind, Except.bind, Except.map, Except.mapError] at accepted
  | ok native =>
    simp only [projected, bind, Except.bind, pure, Except.pure] at accepted
    split at accepted <;> simp only [Except.map, Except.mapError] at accepted
    · cases accepted; rfl
    · cases accepted

theorem metadata_of_read {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : ExpressionId} {node : ExpressionNode} {type : Core.Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readExpression checked source id = .ok (node, type)) :
    Metadata checked source id node type := by
  by_cases owner : id.occurrence.owner = source.owner
  · cases found : source.lookupExpression? id with
    | none => simp [SourceCoreCompatibleDataExpressions.readExpression, owner, found, bind, Except.bind] at accepted
    | some actual =>
      by_cases requirements : actual.requirements = []
      · by_cases coercions : actual.coercions = []
        · cases projected : SourceCoreCompatibleDataExpressions.projectType checked (.occurrence id.occurrence) actual.type with
          | error error => simp [SourceCoreCompatibleDataExpressions.readExpression, owner, found, requirements, coercions,
              projected, bind, Except.bind, pure, Except.pure] at accepted
          | ok native =>
            simp [SourceCoreCompatibleDataExpressions.readExpression, owner, found, requirements, coercions,
              projected, bind, Except.bind, pure, Except.pure] at accepted
            obtain ⟨rfl, rfl⟩ := accepted
            exact ⟨found, owner, requirements, coercions, projectType_of_accepted projected⟩
        · simp [SourceCoreCompatibleDataExpressions.readExpression, owner, found, requirements, coercions,
            bind, Except.bind, pure, Except.pure] at accepted
      · simp [SourceCoreCompatibleDataExpressions.readExpression, owner, found, requirements,
          bind, Except.bind, pure, Except.pure] at accepted
  · simp [SourceCoreCompatibleDataExpressions.readExpression, owner, bind, Except.bind] at accepted

inductive Literal (fuel : Nat) (context : ValuesContext) (node : ExpressionNode)
    (type : TypeSystem.Ty) (value : SourceCoreCompatibleValues.Value) (code : Core.Expr) : Prop where
  | encoded (output : SourceCoreCompatibleValues.Encoded fuel context type value)
      (accepted : SourceCoreCompatibleValues.encode fuel context type value = .ok output)
      (unchanged : output.context.registry.entries = context.registry.entries)
      (quoted : SourceCoreCompatibleDataExpressions.quote output.value = some code) :
      Literal fuel context node type value code

theorem literal_of_accepted {fuel : Nat} {context : ValuesContext} {node : ExpressionNode}
    {type : TypeSystem.Ty} {value : SourceCoreCompatibleValues.Value} {code : Core.Expr}
    (accepted : SourceCoreCompatibleDataExpressions.staticValue fuel context node type value = .ok code) :
    Literal fuel context node type value code := by
  unfold SourceCoreCompatibleDataExpressions.staticValue at accepted
  cases encodedBy : SourceCoreCompatibleValues.encode fuel context type value with
  | error error => simp [encodedBy, Except.mapError, bind, Except.bind] at accepted
  | ok encoded =>
    simp only [encodedBy, Except.mapError, bind, Except.bind] at accepted
    split at accepted <;> try cases accepted
    rename_i unchanged
    cases quoted : SourceCoreCompatibleDataExpressions.quote encoded.value with
    | none => simp [quoted] at accepted
    | some expression =>
      simp only [quoted, pure, Except.pure, Except.ok.injEq] at accepted
      subst code
      exact .encoded encoded encodedBy unchanged quoted

inductive ReadCode (fuel : Nat) (context : ValuesContext) (node : ExpressionNode)
    (declared : TypedBinder) (index : Nat) (type : Core.Ty) (reason : Core.Word) : Core.Expr → Prop where
  | ordinary (notMapping : ¬ ∃ key value, declared.scheme.body = .mapping key value) :
      ReadCode fuel context node declared index type reason (Core.OptionalCell.read type (.var index) reason)
  | mapping {key value : TypeSystem.Ty} {literal : Core.Expr}
      (declaredType : declared.scheme.body = .mapping key value)
      (generated : Literal fuel context node declared.scheme.body (.mapping key value []) literal) :
      ReadCode fuel context node declared index type reason
        (SourceCoreCompatibleDataExpressions.readMapping (.var index) literal)

structure Certificate (fuel : Nat) (context : ValuesContext) (source : TypedSource)
    (scope : Scope) (id : ExpressionId) (reason : Core.Word) (code : Core.Expr) where
  node : ExpressionNode
  type : Core.Ty
  binder : Resolved.LocalId
  name : String
  declared : TypedBinder
  index : Nat
  metadata : Metadata context.checked source id node type
  form : node.form = .reference name (.local binder)
  binderOwner : binder.owner = source.owner
  slot : SourceCoreLocalCell.lookup? scope binder = some (index, type)
  declaration : SourceCoreDataPlaces.rootBinder source binder = .ok declared
  emitted : ReadCode fuel context node declared index type reason code

theorem of_accepted {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Core.Word} {code : Core.Expr}
    (accepted : SourceCoreCompatibleDataExpressions.lowerRead fuel context source scope id reason = .ok code) :
    Nonempty (Certificate fuel context source scope id reason code) := by
  unfold SourceCoreCompatibleDataExpressions.lowerRead at accepted
  obtain ⟨⟨node, type⟩, read, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  cases form : node.form <;> simp only [form] at accepted <;> try cases accepted
  case reference name resolution =>
    cases resolution <;> simp only at accepted <;> try cases accepted
    case «local» binder =>
      simp only [pure, Except.pure, bind, Except.bind] at accepted
      split at accepted <;> try cases accepted
      rename_i binderOwner
      cases slot : SourceCoreLocalCell.lookup? scope binder with
      | none => simp [slot] at accepted
      | some pair =>
        obtain ⟨index, payload⟩ := pair
        simp only [slot] at accepted
        obtain ⟨ensured, ensuredBy, accepted⟩ := bind_ok accepted
        cases ensured
        have sameType : type = payload := by
          unfold SourceCoreBasic.ensureType at ensuredBy
          split at ensuredBy
          · assumption
          · cases ensuredBy
        subst payload
        obtain ⟨declared, declaration, accepted⟩ := bind_ok accepted
        let base := Certificate.mk (fuel := fuel) (reason := reason) (code := code) node type binder name declared index (metadata_of_read read) form
          (by simpa using binderOwner) slot declaration
        cases declaredType : declared.scheme.body <;> simp only [declaredType] at accepted
        all_goals try (cases accepted; exact ⟨base (.ordinary (by simp [declaredType]))⟩)
        case mapping key value =>
          obtain ⟨literal, generated, accepted⟩ := bind_ok accepted
          cases accepted
          exact ⟨base (.mapping declaredType (by
            rw [declaredType]
            exact literal_of_accepted generated))⟩

/-- The actual declaration lookup excludes generalized and qualified cells. -/
theorem Certificate.monomorphic {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Core.Word} {code : Core.Expr}
    (certificate : Certificate fuel context source scope id reason code) :
    certificate.declared.scheme.quantified = [] := by
  have accepted := certificate.declaration
  by_cases owner : certificate.binder.owner = source.owner
  · cases found : (SourceCoreDataPlaces.declaredBinders source).filter
        (fun binder => decide (binder.id = certificate.binder)) with
    | nil => simp [SourceCoreDataPlaces.rootBinder, owner, found] at accepted
    | cons head rest => cases rest with
      | cons => simp [SourceCoreDataPlaces.rootBinder, owner, found] at accepted
      | nil =>
        by_cases mono : head.scheme.quantified = []
        · by_cases requirements : head.schemeRequirements = []
          · simp [SourceCoreDataPlaces.rootBinder, owner, found, mono, requirements,
              pure, Except.pure] at accepted
            subst head
            exact mono
          · simp [SourceCoreDataPlaces.rootBinder, owner, found, mono, requirements,
              bind, Except.bind, pure, Except.pure] at accepted
        · simp [SourceCoreDataPlaces.rootBinder, owner, found, mono, bind, Except.bind] at accepted
  · simp [SourceCoreDataPlaces.rootBinder, owner, bind, Except.bind] at accepted

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralCertificates
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralMeaning
/-! Independent literal correspondence under arbitrary ambient definitions.
The shared proof takes the selected numeric requirement judgments directly.
The original ordinary-context entry remains an adapter with its full ledger
and covering dictionary. Literal code preserves every environment and heap,
including administrative closures in other cells. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiterals
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

structure ContextValid (solved : List SolvedRequirement) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) : Prop where
  ledger : context.solvedRequirements = solved
  valid : RequirementLedgerWellFormed context
  covers : evidence.Covers context

private theorem ContextValid.proves {solved : List SolvedRequirement} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} (valid : ContextValid solved context evidence)
    {id : RequirementId} {predicate : ProgramPredicate}
    (member : ∃ entry ∈ solved, entry.id = id ∧ entry.predicate = predicate) :
    RequirementProves context id predicate := by
  obtain ⟨entry, member, identifier, predicate⟩ := member
  have present : entry ∈ context.solvedRequirements := by rw [valid.ledger]; exact member
  exact ⟨entry, ⟨present, identifier⟩, predicate, valid.valid.entriesValid entry present⟩

/-- Independent evidence for the numeric form at this occurrence. These are
requirement judgments, not source or native execution laws. Non-numeric leaves
have no numeric obligation. -/
def NumericEvidence (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (node : ExpressionNode) : Prop :=
  ∀ literal resolution, node.form = .integerLiteral literal resolution →
    RequirementProves context resolution.requirement resolution.predicate ∧
    ¬ Dynamic.RequirementUnavailable context evidence resolution.requirement

private theorem ContextValid.numeric {solved : List SolvedRequirement} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} (valid : ContextValid solved context evidence)
    {node : ExpressionNode} {type code} (literal : Literal solved node type code) :
    NumericEvidence context evidence node := by
  intro value resolution form
  cases literal with
  | unit other _ _ _ => rw [other] at form; cases form
  | bool _ other _ _ _ => rw [other] at form; cases form
  | word _ other _ _ _ _ => rw [other] at form; cases form
  | resolvedWord other metadata | resolvedInteger other metadata =>
    have same := other.symm.trans form
    cases same
    have proves := valid.proves metadata.solved
    obtain ⟨closed, produced⟩ := Dynamic.RequirementProves.produces_of_covers valid.covers proves
    exact ⟨by simpa only [IntegerLiteralResolution.predicate, metadata.targetType] using proves,
      produced.excludes_unavailable valid.valid.idsUnique⟩

private theorem word_constructs {span : Syntax.SourceSpan} {literal : Syntax.CoreLiteralValue} {value : Word}
    (meaning : WordLiteralDenotes ⟨span, literal⟩ value) : Dynamic.LiteralConstructs literal (.word value) := by
  have modulo : Word.ofNatModulo value.val = value := by apply Fin.ext; exact Nat.mod_eq_of_lt value.isLt
  rw [← modulo]
  exact .word meaning

private theorem contains_unique {source : TypedSource} {id : ExpressionId} {left right : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (first : ContainsExpression source id left)
    (second : ContainsExpression source id right) : left = right :=
  Option.some.inj ((lookupExpression?_complete unique first).symm.trans (lookupExpression?_complete unique second))

private theorem Atomic.not_local {form : ExpressionForm} (atomic : Atomic form) :
    ∀ name binder, form ≠ .reference name (.local binder) := by
  cases atomic <;> intros <;> intro impossible <;> cases impossible

private theorem Literal.atomic {solved node type code} (literal : Literal solved node type code) : Atomic node.form := by
  cases literal with
  | unit form _ _ _ => rw [form]; exact .unit
  | bool value form _ _ _ => rw [form]; exact .bool _ _
  | word value form _ _ _ _ => rw [form]; exact .word _
  | resolvedWord form _ | resolvedInteger form _ => rw [form]; exact .integer _ _

private theorem Literal.coercions {solved node type code} (literal : Literal solved node type code) : node.coercions = [] := by
  cases literal with
  | unit _ _ _ empty | bool _ _ _ _ empty | word _ _ _ _ empty _ => exact empty
  | resolvedWord _ metadata | resolvedInteger _ metadata => exact metadata.coercions

private theorem evaluation_raw
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (atomic : Atomic node.form) (empty : node.coercions = [])
    (evaluation : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    Dynamic.ExpressionFormEvaluates program context evidence source environment before node.form node.requirements node.coercions value after := by
  cases evaluation with
  | intro found raw coercions =>
    have same := contains_unique unique found contains
    subst same
    rw [empty] at coercions
    cases coercions
    exact raw
  | generalizedLocal found form _ _ _ _ _ _ _ =>
    have same := contains_unique unique found contains
    subst same
    exact False.elim (atomic.not_local _ _ form)

private theorem fault_raw
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (atomic : Atomic node.form) (empty : node.coercions = [])
    (fault : Dynamic.ExpressionFaults program context evidence source environment before id reason after) :
    Dynamic.ExpressionFormFaults program context evidence source environment before node.form node.requirements node.coercions reason after := by
  cases fault with
  | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
  | form found raw => exact contains_unique unique found contains ▸ raw
  | coercion found _ failed =>
    have same := contains_unique unique found contains
    subst same
    rw [empty] at failed
    cases failed
  | generalizedLocalRequirement found form _ _ _ _ _ _ _ | generalizedLocalCoercion found form _ _ _ _ _ _ _ =>
    have same := contains_unique unique found contains
    subst same
    exact False.elim (atomic.not_local _ _ form)

private theorem Literal.form_unique {solved : List SolvedRequirement} {node : ExpressionNode} {type code}
    (literal : Literal solved node type code)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap firstHeap secondHeap : Dynamic.Heap}
    {left right : Dynamic.Value}
    (first : Dynamic.ExpressionFormEvaluates program context evidence source environment heap node.form node.requirements node.coercions left firstHeap)
    (second : Dynamic.ExpressionFormEvaluates program context evidence source environment heap node.form node.requirements node.coercions right secondHeap) :
    left = right ∧ firstHeap = secondHeap := by
  cases literal with
  | unit form _ _ _ =>
    rw [form] at first second
    cases first with | tuple _ elements pack =>
      cases elements
      cases pack
      cases second with | tuple _ elements pack => cases elements; cases pack; exact ⟨rfl, rfl⟩
  | bool value form _ _ _ => rw [form] at first second; cases first; cases second; exact ⟨rfl, rfl⟩
  | word value form _ _ _ _ =>
    rw [form] at first second
    cases first with | literal _ first =>
      cases second with | literal _ second => exact ⟨first.functional second, rfl⟩
  | resolvedWord form _ | resolvedInteger form _ =>
    rw [form] at first second
    cases first with | integerLiteral _ first =>
      cases second with | integerLiteral _ second => exact ⟨first.functional second, rfl⟩

private theorem Literal.excludes_fault_with_evidence {solved : List SolvedRequirement} {node : ExpressionNode} {type code}
    (literal : Literal solved node type code)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    (valid : NumericEvidence context evidence node)
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (fault : Dynamic.ExpressionFormFaults program context evidence source environment before node.form node.requirements node.coercions reason after) : False := by
  cases literal with
  | unit form _ _ _ =>
    rw [form] at fault
    cases fault with | tuple _ failed => cases failed
  | bool value form _ _ _ | word value form _ _ _ _ => rw [form] at fault; cases fault
  | resolvedWord form metadata | resolvedInteger form metadata =>
    rw [form] at fault
    cases fault with | integerRequirement _ unavailable =>
      exact (valid _ _ form).2 unavailable

private theorem Literal.excludes_fault {solved : List SolvedRequirement} {node : ExpressionNode} {type code}
    (literal : Literal solved node type code)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    (valid : ContextValid solved context evidence)
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (fault : Dynamic.ExpressionFormFaults program context evidence source environment before node.form node.requirements node.coercions reason after) : False :=
  literal.excludes_fault_with_evidence (valid.numeric literal) fault

/-- Atomic code is well typed in every ambient definition environment. -/
theorem Literal.hasType {solved node type code} (literal : Literal solved node type code)
    (context : Core.Context) (definitions : DataEnvironment) :
    HasType context code (LanguageResult.resultType type) definitions := by
  cases literal with
  | unit => exact .inRight .word .unit
  | bool => exact .inRight .word .bool
  | word | resolvedWord => exact .inRight .word .word
  | resolvedInteger => exact .inRight .word .integer

/-- Each static literal constructs a source value and a native value directly.
The environment renaming and both heaps are arbitrary. -/
theorem Literal.evaluates_with_evidence {solved : List SolvedRequirement} {node : ExpressionNode} {type code}
    (literal : Literal solved node type code)
    {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (valid : NumericEvidence context evidence node)
    (source : TypedSource) (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    (mapping : LocationMap) (world : StoreTyping) (native : Environment) (store : Store) (ξ : Renaming) :
    ∃ sourceValue coreValue,
      Dynamic.ExpressionFormEvaluates program context evidence source environment heap node.form node.requirements node.coercions sourceValue heap ∧
      ValueRep checked registry functions mapping world node.type sourceValue coreValue type ∧
      Evaluates native store (code.rename ξ) (.inRight .word coreValue) store := by
  cases literal with
  | unit form type requirements coercions =>
    rw [form, type, requirements, coercions]
    exact ⟨_, _, .tuple rfl .nil .nil, .unit, .inRight .unit⟩
  | bool value form type requirements coercions =>
    rw [form, type, requirements, coercions]
    exact ⟨_, _, .builtinBoolean rfl, .bool _, .inRight .bool⟩
  | word value form type requirements coercions meaning =>
    rw [form, type, requirements, coercions]
    exact ⟨_, _, .literal rfl (word_constructs meaning), .word _, .inRight .word⟩
  | @resolvedWord value resolution validated form metadata =>
    have constructs : Dynamic.ResolvedIntegerLiteralConstructs context value resolution (.word (Word.ofNatModulo resolution.rawValue)) := by
      cases resolution with | mk raw target requirement =>
        have targetEq := metadata.targetType
        dsimp only at targetEq
        subst target
        exact .word metadata.meaning (valid _ _ form).1
    rw [form, metadata.nodeType, metadata.requirements, metadata.coercions, metadata.value]
    exact ⟨_, _, .integerLiteral rfl constructs, .word _, .inRight .word⟩
  | @resolvedInteger value resolution validated form metadata =>
    have constructs : Dynamic.ResolvedIntegerLiteralConstructs context value resolution (.integer (Int.ofNat resolution.rawValue)) := by
      cases resolution with | mk raw target requirement =>
        have targetEq := metadata.targetType
        dsimp only at targetEq
        subst target
        exact .integer metadata.meaning (valid _ _ form).1
    rw [form, metadata.nodeType, metadata.requirements, metadata.coercions, metadata.value]
    exact ⟨_, _, .integerLiteral rfl constructs, .integer _, .inRight .integer⟩

theorem Literal.evaluates {solved : List SolvedRequirement} {node : ExpressionNode} {type code}
    (literal : Literal solved node type code)
    {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (valid : ContextValid solved context evidence)
    (source : TypedSource) (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    (mapping : LocationMap) (world : StoreTyping) (native : Environment) (store : Store) (ξ : Renaming) :
    ∃ sourceValue coreValue,
      Dynamic.ExpressionFormEvaluates program context evidence source environment heap node.form node.requirements node.coercions sourceValue heap ∧
      ValueRep checked registry functions mapping world node.type sourceValue coreValue type ∧
      Evaluates native store (code.rename ξ) (.inRight .word coreValue) store :=
  literal.evaluates_with_evidence functions program context evidence (valid.numeric literal)
    source environment heap mapping world native store ξ

/-- Universal literal preservation has no child execution hypothesis. -/
theorem preserves_with_evidence {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    {solved : List SolvedRequirement} (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment)
    {certificate : SourceCoreLocalCell.Scope → ExpressionId → SourceCoreBasic.LoweredExpr → Prop}
    {source : TypedSource}
    (receipts : ∀ scope id lowered, certificate scope id lowered →
      ∃ node, source.lookupExpression? id = some node ∧ Literal solved node lowered.type lowered.expression ∧
        NumericEvidence context evidence node)
    (unique : NodeOccurrencesUnique source) (faults : FunctionCalls.FaultRep) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults := by
  intro scope id lowered receipt node found mapping world administrative environment canonical actual before store ξ outcome after
    environments heaps locals agrees trace
  obtain ⟨other, otherFound, literal, valid⟩ := receipts scope id lowered receipt
  have same := Option.some.inj (otherFound.symm.trans found)
  subst other
  obtain ⟨sourceValue, coreValue, raw, represented, evaluated⟩ :=
    literal.evaluates_with_evidence functions program context evidence valid source environment before mapping world actual store ξ
  have contains := lookupExpression?_sound found
  have result : outcome = .value sourceValue ∧ after = before := by
    cases trace with
    | value trace =>
      have actualRaw := evaluation_raw unique contains literal.atomic literal.coercions trace
      obtain ⟨rfl, rfl⟩ := literal.form_unique actualRaw raw
      exact ⟨rfl, rfl⟩
    | fault fault =>
      exact False.elim (literal.excludes_fault_with_evidence valid (fault_raw unique contains literal.atomic literal.coercions fault))
  obtain ⟨rfl, rfl⟩ := result
  exact ⟨coreValue |> Value.inRight .word, store, mapping, world, evaluated, .value represented,
    heaps, .refl _, .refl _, .refl _ _, .refl _⟩

theorem preserves {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    {solved : List SolvedRequirement} (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (valid : ContextValid solved context evidence)
    {source : TypedSource} (unique : NodeOccurrencesUnique source) (faults : FunctionCalls.FaultRep) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (fun _ id lowered => Certificate solved source id lowered) faults := by
  refine preserves_with_evidence (registry := registry) (solved := solved) functions program context evidence (certificate := fun _ id lowered => Certificate solved source id lowered) ?_ unique faults
  intro scope id lowered receipt
  obtain ⟨node, found, literal⟩ := receipt
  exact ⟨node, found, literal, valid.numeric literal⟩

/-- A completed native literal always reconstructs its independent source
execution, without assuming any source trace beforehand. -/
theorem reflects_with_evidence {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    {solved : List SolvedRequirement} (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    {certificate : SourceCoreLocalCell.Scope → ExpressionId → SourceCoreBasic.LoweredExpr → Prop}
    (receipts : ∀ scope id lowered, certificate scope id lowered →
      ∃ node, source.lookupExpression? id = some node ∧ Literal solved node lowered.type lowered.expression ∧
        NumericEvidence context evidence node) (faults : FunctionCalls.FaultRep) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults := by
  intro scope id lowered receipt node found mapping world administrative environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluation
  obtain ⟨other, otherFound, literal, valid⟩ := receipts scope id lowered receipt
  have same := Option.some.inj (otherFound.symm.trans found)
  subst other
  obtain ⟨sourceValue, coreValue, raw, represented, evaluated⟩ :=
    literal.evaluates_with_evidence functions program context evidence valid source environment before mapping world actual store ξ
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated evaluation
  have trace : Dynamic.ExpressionEvaluates program context evidence source environment before id sourceValue before := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found) raw
    rw [literal.coercions]
    exact .nil
  exact ⟨.value sourceValue, before, mapping, world, .value trace, .value represented,
    heaps, .refl _, .refl _, .refl _ _, .refl _⟩

theorem reflects {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    {solved : List SolvedRequirement} (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (valid : ContextValid solved context evidence)
    (source : TypedSource) (faults : FunctionCalls.FaultRep) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (fun _ id lowered => Certificate solved source id lowered) faults := by
  refine reflects_with_evidence (registry := registry) (solved := solved) functions program context evidence source (certificate := fun _ id lowered => Certificate solved source id lowered) ?_ faults
  intro scope id lowered receipt
  obtain ⟨node, found, literal⟩ := receipt
  exact ⟨node, found, literal, valid.numeric literal⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiterals
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualLiterals
/-! The real contextual traversal supplies the atomic literal certificate.
Catalog exclusion and exact empty coercions identify the ordinary emission
path, including the dedicated native numeric-evidence branch. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiterals
open Core Frontend SourceInference

/-- Original numeric requirement IDs are retained; ordinary leaves have none. -/
def owned (form : ExpressionForm) : List RequirementId := match form with
  | .integerLiteral _ resolution => [resolution.requirement]
  | _ => []

private theorem contextualSource_atomic
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceSpecialization.SpecializationKey)
    (parent : Option SourceCoreLocalEvidence.Prepared) {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) (atomic : Atomic node.form) :
    SourceCoreGeneralFunctions.contextualSource program plan locals owner parent source id = .ok source := by
  generalize form : node.form = shape at atomic
  cases atomic <;> simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]

private theorem evidence_atomic (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (context : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (fuel : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (atomic : Atomic node.form)
    (requirements : node.requirements = owned node.form) (coercions : node.coercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller context child fuel source scope id reasonAt callables = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node = some (owned node.form) := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    change (if (owned node.form).length < 0 then none else
      if owned node.form = (owned node.form).take ((owned node.form).length - 0) ++ [] then
        some ((owned node.form).take ((owned node.form).length - 0)) else none) = _
    simp
  generalize form : node.form = shape at atomic
  cases atomic <;> simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
    owned, bind, Except.bind, pure, Except.pure]

private theorem bind_accepted {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- This theorem extracts a semantic certificate from the actual contextual
compiler result. It excludes generalized initializer overrides and output
coercions by their source metadata, without any child-evaluation premise. -/
theorem of_contextual
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {context : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (atomic : Atomic node.form)
    (unitType : node.form = .tuple [] → node.type = .unit)
    (requirements : node.requirements = owned node.form) (coercions : node.coercions = [])
    (notInitializer : locals.bindings.find? (fun binding => decide (binding.caller = context.owner ∧ binding.initializer = id)) = none)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics context native parent skipInitializer fuel source scope id reasonAt = .ok lowered) :
    Certificate context.solvedRequirements source id lowered := by
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
  | succ fuel =>
    rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
    cases parent with
    | some prepared =>
      dsimp only at accepted
      simp only [bind, Except.bind, pure, Except.pure] at accepted
      refine of_functions (values := values) found atomic unitType ?_ ?_ ?_ accepted
      · intro child budget
        dsimp only
        rw [contextualSource_atomic program context.plan locals context.owner (some prepared) found atomic]
        simp only [found, notInitializer, Option.filter]
        rw [evidence_atomic program _ prepared.caller context child budget scope reasonAt _ found atomic requirements coercions]
        generalize form : node.form = shape at atomic
        cases atomic <;> simp only [form]
      · change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner (some prepared) source id
          representation.expressions.readExpression viewed id) = _
        rw [contextualSource_atomic program context.plan locals context.owner (some prepared) found atomic]
        simp only [bind, Except.bind, readPolicy]
      · exact leafPolicy
    | none =>
      dsimp only at accepted
      obtain ⟨caller, selected, generated⟩ := bind_accepted accepted
      refine of_functions (values := values) found atomic unitType ?_ ?_ ?_ generated
      · intro child budget
        dsimp only
        rw [contextualSource_atomic program context.plan locals context.owner none found atomic]
        simp only [bind, Except.bind, pure, Except.pure, found, notInitializer, Option.filter]
        rw [evidence_atomic program _ caller context child budget scope reasonAt _ found atomic requirements coercions]
        generalize form : node.form = shape at atomic
        cases atomic <;> simp only [form]
      · change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner none source id
          representation.expressions.readExpression viewed id) = _
        rw [contextualSource_atomic program context.plan locals context.owner none found atomic]
        simp only [bind, Except.bind, readPolicy]
      · exact leafPolicy

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiterals
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadFaultPolicies
/-! An ordinary read fault policy consumes the actual Source binding
and current uninitialized cell. No diagnostic table or fault relation is
inferred from a native representation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
open Core Frontend SourceInference

/-- The exact Source occurrence, lexical binding and current cell at the
ordinary uninitialized branch of an accepted read. -/
structure UninitializedWitness {fuel : Nat} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId}
    {reason : Word} {code : Expr}
    (certificate : Certificate fuel values source scope id reason code)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (heap : Dynamic.Heap) (location : Dynamic.Location) (cell : Dynamic.Cell) : Prop where
  contains : ContainsExpression source id certificate.node
  localReference : certificate.node.form = .reference certificate.name (.local certificate.binder)
  declaration : Resolved.LocalScope.Lookup context.locals certificate.binder certificate.declared.scheme
  occurrenceView : SourceCoreRawMetadata.runtimeType certificate.node.type =
    SourceCoreRawMetadata.runtimeType certificate.declared.scheme.body
  lookup : Dynamic.Environment.LooksUp environment certificate.binder location
  read : Dynamic.Heap.Reads heap location cell
  cellType : cell.type = certificate.declared.scheme.body
  ordinary : cell.generalized = none
  empty : cell.value = none
  notMapping : ¬ ∃ key value, cell.type = .mapping key value

/-- Inclusion is requested only for the location selected by this actual read.
The real environment, heap and lexical context remain explicit indices. -/
def UninitializedPolicy {fuel : Nat} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId}
    {reason : Word} {code : Expr}
    (certificate : Certificate fuel values source scope id reason code)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (heap : Dynamic.Heap) (faults : Dynamic.SemanticFault → Word → Prop) : Prop :=
  ∀ location cell, UninitializedWitness certificate context environment heap location cell →
    faults (.uninitializedLocation location) reason

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLeaves
/-! Actual compatible local reads over the complete native definition table.
The pure encoder receipt constructs a lazy mapping value; reading an ordinary
cell either returns its authenticated payload or produces the specified fault.
No child runtime premise or assumption of whole-source determinism is used. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleMapping.VirtualRoot

private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible

/-- Actual successful encoding supplies the original source metadata relation
under any ambient function model; this data encoder creates no function leaf. -/
theorem Literal.represents {fuel : Nat} {context : ValuesContext} {node : ExpressionNode}
    {sourceType : TypeSystem.Ty} {carrier : SourceCoreCompatibleValues.Value} {code : Expr}
    (literal : Literal fuel context node sourceType carrier code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    {sourceValue : Dynamic.Value} (meaning : CompatibleEncoding.Means carrier sourceValue)
    (mapping : LocationMap) (world : StoreTyping) :
    ∃ value type, Quoted value code ∧
      ValueRep context.checked registry functions mapping world sourceType sourceValue value type := by
  cases literal with
  | encoded encoded accepted unchanged quoted =>
    have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions context.checked.catalog)
      accepted meaning mapping world
    have represented := represented.extend (return_registry encoded unchanged) (.refl _) (.refl _)
    have extended := ValueRep.map_functions (future := functions)
      (fun impossible => False.elim impossible) represented
    exact ⟨_, _, quoted_of_quote quoted, extended.extend extension (.refl _) (.refl _)⟩

/-- The source scope fixes the raw declaration type separately from its native
projection. Occurrence views may erase staging wrappers, but keep their own
original source type in the result relation. -/
structure StaticBinding {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    (sourceContext : SourceSemantics.Context) : Prop where
  declared : Resolved.LocalScope.Lookup sourceContext.locals certificate.binder certificate.declared.scheme
  occurrence : SourceCoreRawMetadata.runtimeType certificate.node.type =
    SourceCoreRawMetadata.runtimeType certificate.declared.scheme.body

private theorem monomorphic_instance {context : SourceSemantics.Context}
    {scheme : TypeSystem.Scheme} {type : TypeSystem.Ty}
    (monomorphic : scheme.quantified = [])
    (instantiates : SchemeInstantiatesAt context scheme type) : scheme.body = type := by
  cases instantiates with
  | intro _ substitution exactDomain _ result =>
    have emptyDomain : substitution.domain = [] := by
      have permutation := exactDomain.domain_permutation
      rw [monomorphic] at permutation
      exact List.perm_nil.mp permutation
    have empty : substitution = [] := by
      cases substitution with
      | nil => rfl
      | cons head tail => simp [TypeSystem.Substitution.domain] at emptyDomain
    subst substitution
    simpa [SchemeInstantiates.empty_apply] using result

/-- The independent source typing judgment supplies the declaration/occurrence
agreement. Equal native projections are not used to recover source metadata. -/
theorem StaticBinding.of_expression_type {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declared : Resolved.LocalScope.Lookup sourceContext.locals certificate.binder certificate.declared.scheme)
    (typed : ExpressionHasType source sourceContext id certificate.node.type) :
    StaticBinding certificate sourceContext := by
  refine ⟨declared, ?_⟩
  generalize nodeType : certificate.node.type = occurrenceType at typed
  cases typed with
  | @intro _ _ node rawType plan contains formTyped rawEq _ _ requirements =>
    have found := lookupExpression?_complete unique contains
    have same := Option.some.inj (found.symm.trans certificate.metadata.found)
    subst node
    have path := requirements.outputPath
    rw [certificate.metadata.coercions] at path
    cases path
    rw [certificate.form] at formTyped
    cases formTyped with
    | reference valid =>
      generalize binderEq : certificate.binder = binderId at valid
      cases valid with
      | «local» lookup _ instantiation =>
        rw [binderEq] at declared
        have schemeEq := lookup.value_unique declared
        have instantiates := instantiation.toSchemeInstantiatesAt
        rw [schemeEq] at instantiates
        exact congrArg SourceCoreRawMetadata.runtimeType
          (monomorphic_instance certificate.monomorphic instantiates).symm

private theorem cells_write_exists {cells : List Dynamic.Cell} {index : Nat} {cell : Dynamic.Cell}
    (found : Dynamic.Heap.CellAt cells index cell) (value : Dynamic.Value) : ∃ updated,
      Dynamic.Heap.CellsWrite cells index {cell with value := some value} updated := by
  induction found with
  | head => exact ⟨_, .head⟩
  | tail _ ih => obtain ⟨updated, written⟩ := ih; exact ⟨_, .tail written⟩

private theorem writes_exists {heap : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell}
    (read : Dynamic.Heap.Reads heap location cell) (value : Dynamic.Value) :
    ∃ after, Dynamic.Heap.Writes heap location (some value) after := by
  cases read with
  | intro selected =>
    obtain ⟨updated, written⟩ := cells_write_exists selected value
    exact ⟨⟨updated⟩, .intro (.intro selected) written⟩

private theorem ordinary_rename (type : Ty) (index : Nat) (reason : Word) (ξ : Renaming) :
    (OptionalCell.read type (.var index) reason).rename ξ = OptionalCell.read type (.var (ξ index)) reason := rfl

private theorem Quoted.rename {value : Value} {code : Expr} (quoted : Quoted value code) (ξ : Renaming) :
    code.rename ξ = code := by
  induction quoted generalizing ξ <;> simp_all [Expr.rename]

private theorem mapping_rename {value : Value} {literal : Expr} (quoted : Quoted value literal)
    (index : Nat) (ξ : Renaming) :
    (SourceCoreCompatibleDataExpressions.readMapping (.var index) literal).rename ξ =
      SourceCoreCompatibleDataExpressions.readMapping (.var (ξ index)) literal := by
  have pureLiteral := quoted.weaken 0
  simp only [SourceCoreCompatibleDataExpressions.readMapping, pureLiteral]
  simp only [Expr.rename, Quoted.rename quoted, Renaming.lift, LanguageResult.success]

/-- An actual accepted read and its static source binding construct both finite
executions and the resulting heap/frame correspondence. Mapping initialization
updates the existing mapped cell; it allocates no administrative cell. -/
theorem Certificate.evaluates_with_diagnostics {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep} (uninitialized : UninitializedPolicy certificate sourceContext environment heap faults) :
    ∃ outcome after value finalStore,
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after ∧
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
  rcases certificate with ⟨node, type, binder, name, declared, index, metadata, form, binderOwner, slot, declaration, emitted⟩
  rcases binding with ⟨declaredScope, occurrence⟩
  dsimp only at *
  obtain ⟨location, cell, lookup, read, cellType, _⟩ := locals.lookup declaredScope
  obtain ⟨target, selected, optional, nativeLookup, reference, selectedRead, nativeRead, represented⟩ :=
    GenericHeap.lookup_visible environments heaps lookup slot
  have sameCell := read.functional selectedRead
  subst selected
  have representedAt : ∀ {sourceValue native},
      ValueRep context.checked registry functions mapping world cell.type sourceValue native type →
      ValueRep context.checked registry functions mapping world node.type sourceValue native type := by
    intro sourceValue native related
    exact .compatible (cellType ▸ occurrence) related
  have contains := lookupExpression?_sound metadata.found
  have sourceSuccess : ∀ {value after},
      Dynamic.ExpressionFormEvaluates program sourceContext evidence source environment heap
        node.form [] [] value after →
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id (.value value) after := by
    intro value after form
    exact .value (.intro contains (by rw [metadata.requirements, metadata.coercions]; exact form)
      (by rw [metadata.coercions]; exact .nil))
  have sourceFault : ∀ {fault after},
      Dynamic.ExpressionFormFaults program sourceContext evidence source environment heap
        node.form [] [] fault after →
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id (.fault fault) after := by
    intro fault after form
    exact .fault (.form contains (by rw [metadata.requirements, metadata.coercions]; exact form))
  cases represented with
  | @initialized sourceType _ sourceValue native payload =>
    have sourceEvaluated := sourceSuccess (form ▸
      (Dynamic.ExpressionFormEvaluates.local (coercions := []) rfl lookup read rfl rfl))
    refine ⟨_, heap, .inRight .word native, store, sourceEvaluated, ?_,
      .value (representedAt payload), heaps, (fun _ _ _ => ⟨by assumption, rfl⟩), .refl _⟩
    cases emitted with
    | ordinary _ =>
      rw [ordinary_rename]
      exact OptionalCell.read_success reason (.var (agrees nativeLookup)) nativeRead
    | mapping declared generated =>
      obtain ⟨_, _, quoted, _⟩ := generated.represents functions extension (.mapping .empty) mapping world
      rw [mapping_rename quoted]
      exact SourceCoreCompatibleDataExpressions.readMapping_present (.var (agrees nativeLookup)) nativeRead
  | @uninitialized sourceType _ projected =>
    change sourceType = declared.scheme.body at cellType
    cases emitted with
    | ordinary notMapping =>
      refine ⟨.fault (.uninitializedLocation location), heap, .inLeft type (.word reason), store,
        sourceFault (form ▸ (.localUninitialized (owned := []) rfl lookup read rfl rfl ?_)), ?_,
        .fault (uninitialized location _ ⟨contains, form, declaredScope, occurrence, lookup, read,
          cellType, rfl, rfl, by simpa only [cellType] using notMapping⟩), heaps, (fun _ _ _ => ⟨by assumption, rfl⟩), .refl _⟩
      · simpa only [cellType] using notMapping
      · rw [ordinary_rename]
        exact OptionalCell.read_failure reason (.var (agrees nativeLookup)) nativeRead
    | @mapping key value literal declared generated =>
      obtain ⟨native, encodedType, quoted, payload⟩ := generated.represents functions extension (.mapping .empty) mapping world
      have same : encodedType = type := Except.ok.inj (payload.projection.symm.trans (cellType ▸ projected))
      subst encodedType
      obtain ⟨after, written⟩ := writes_exists read (.mapping key value [])
      have cellPayload : ValueRep context.checked registry functions mapping world sourceType (.mapping key value []) native type :=
        cellType.symm ▸ payload
      obtain ⟨finalStore, nativeWritten, finalHeaps, frame⟩ := heaps.write_initialized reference read cellPayload written
      have finalEq := (Store.write?_eq_some_iff.mp nativeWritten).2
      refine ⟨.value (.mapping key value []), after, .inRight .word native, finalStore,
        sourceSuccess (form ▸ (.localEmptyMapping rfl lookup read rfl (cellType.trans declared) rfl written)), ?_,
        .value (representedAt cellPayload), finalHeaps, frame, .of_write written⟩
      rw [mapping_rename quoted, finalEq]
      apply SourceCoreCompatibleDataExpressions.readMapping_initializes (.var (agrees nativeLookup)) nativeRead
      · rw [quoted.weaken 0]
        rw [quoted.weaken 0]
        exact quoted.evaluates _ _
      · exact nativeRead

/-- The original uniform inclusion supplies the policy at its actual witness. -/
theorem Certificate.evaluates {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep} (uninitialized : ∀ location, faults (.uninitializedLocation location) reason) :
    ∃ outcome after value finalStore,
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after ∧
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
  exact certificate.evaluates_with_diagnostics functions extension program sourceContext evidence binding
    environments heaps locals agrees (fun location _ _ => uninitialized location)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCompletion
/-! Direct completion of the actual compatible local-read code. The mapping
branch writes the certified empty payload to the same ordinary source cell;
virtual-root getters and generalized cells remain separate interfaces. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCompletion
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleMapping.VirtualRoot

/-- Pure quoted values are recovered by inspecting their original execution.
No second execution or determinism argument is used. -/
theorem quoted_completed {native result : Value} {code : Expr}
    (quoted : Quoted native code) {environment : Environment} {before after : Store}
    (evaluated : Evaluates environment before code result after) : result = native ∧ after = before := by
  induction quoted generalizing environment before result after with
  | unit => cases evaluated; exact ⟨rfl, rfl⟩
  | bool => cases evaluated; exact ⟨rfl, rfl⟩
  | word => cases evaluated; exact ⟨rfl, rfl⟩
  | integer => cases evaluated; exact ⟨rfl, rfl⟩
  | pair _ _ left right =>
    cases evaluated with
    | pair first second =>
      obtain ⟨rfl, rfl⟩ := left first
      obtain ⟨rfl, rfl⟩ := right second
      exact ⟨rfl, rfl⟩
  | inLeft _ _ ih =>
    cases evaluated with
    | inLeft child => obtain ⟨rfl, rfl⟩ := ih child; exact ⟨rfl, rfl⟩
  | inRight _ _ ih =>
    cases evaluated with
    | inRight child => obtain ⟨rfl, rfl⟩ := ih child; exact ⟨rfl, rfl⟩
  | constructed _ _ ih =>
    cases evaluated with
    | construct child => obtain ⟨rfl, rfl⟩ := ih child; exact ⟨rfl, rfl⟩

theorem var_completed {environment : Environment} {before after : Store}
    {index : Nat} {expected result : Value}
    (lookup : environment[index]? = some expected)
    (evaluated : Evaluates environment before (.var index) result after) : result = expected ∧ after = before := by
  cases evaluated with
  | var actual => exact ⟨(Option.some.inj (lookup.symm.trans actual)).symm, rfl⟩

theorem load_completed {environment : Environment} {before after : Store}
    {index target : Nat} {type : Ty} {result : Value}
    (lookup : environment[index]? = some (.cellRef type target))
    (evaluated : Evaluates environment before (.loadCell (.var index)) result after) :
    before.read? target = some result ∧ after = before := by
  cases evaluated with
  | loadCell reference read =>
    obtain ⟨same, rfl⟩ := var_completed lookup reference
    cases same
    exact ⟨read, rfl⟩

/-- The original lazy-read code either keeps its present payload or writes the
quoted empty value to that same cell. The original write determines the final
store, including all unrelated and administrative cells. -/
theorem read_completed {environment : Environment} {before after : Store}
    {index target : Nat} {type : Ty} {optional empty result : Value} {literal : Expr}
    (lookup : environment[index]? = some (.cellRef type target))
    (read : before.read? target = some optional) (quoted : Quoted empty literal)
    (evaluated : Evaluates environment before
      (SourceCoreCompatibleDataExpressions.readMapping (.var index) literal) result after) :
    (∃ annotation payload, optional = .inRight annotation payload ∧ result = .inRight .word payload ∧ after = before) ∨
    (∃ annotation payload, optional = .inLeft annotation payload ∧ result = .inRight .word empty ∧
      before.write? target (.inRight .unit empty) = some after) := by
  unfold SourceCoreCompatibleDataExpressions.readMapping at evaluated
  simp only [quoted.weaken 0] at evaluated
  cases evaluated with
  | letE reference branch =>
    obtain ⟨rfl, rfl⟩ := var_completed lookup reference
    cases branch with
    | caseRight loaded branch =>
      obtain ⟨actualRead, rfl⟩ := load_completed (by rfl) loaded
      cases branch with
      | inRight payload =>
        obtain ⟨rfl, rfl⟩ := var_completed (by rfl) payload
        exact .inl ⟨_, _, Option.some.inj (read.symm.trans actualRead), rfl, rfl⟩
    | caseLeft loaded branch =>
      obtain ⟨actualRead, rfl⟩ := load_completed (by rfl) loaded
      cases branch with
      | letE literalEvaluation writeAndResult =>
        obtain ⟨rfl, rfl⟩ := quoted_completed quoted literalEvaluation
        cases writeAndResult with
        | letE written completed =>
          cases written with
          | storeCell reference _ stored write =>
            obtain ⟨same, rfl⟩ := var_completed (by rfl) reference
            cases same
            cases stored with
            | inRight payload =>
              obtain ⟨rfl, rfl⟩ := var_completed (by rfl) payload
              cases completed with
              | inRight payload =>
                obtain ⟨rfl, rfl⟩ := var_completed (by rfl) payload
                exact .inr ⟨_, _, Option.some.inj (read.symm.trans actualRead), rfl, write⟩

theorem quoted_rename {native : Value} {literal : Expr} (quoted : Quoted native literal) (ξ : Renaming) :
    literal.rename ξ = literal := by
  induction quoted generalizing ξ <;> simp_all [Expr.rename]

theorem mapping_rename {native : Value} {literal : Expr} (quoted : Quoted native literal)
    (index : Nat) (ξ : Renaming) :
    (SourceCoreCompatibleDataExpressions.readMapping (.var index) literal).rename ξ =
      SourceCoreCompatibleDataExpressions.readMapping (.var (ξ index)) literal := by
  simp only [SourceCoreCompatibleDataExpressions.readMapping, quoted.weaken 0]
  simp only [Expr.rename, quoted_rename quoted, Renaming.lift, LanguageResult.success]

theorem cells_write_exists {cells : List Dynamic.Cell} {index : Nat} {cell : Dynamic.Cell}
    (found : Dynamic.Heap.CellAt cells index cell) (value : Dynamic.Value) : ∃ updated,
      Dynamic.Heap.CellsWrite cells index {cell with value := some value} updated := by
  induction found with
  | head => exact ⟨_, .head⟩
  | tail _ ih => obtain ⟨updated, written⟩ := ih; exact ⟨_, .tail written⟩

theorem writes_exists {heap : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell}
    (read : Dynamic.Heap.Reads heap location cell) (value : Dynamic.Value) :
    ∃ after, Dynamic.Heap.Writes heap location (some value) after := by
  cases read with
  | intro selected =>
    obtain ⟨updated, written⟩ := cells_write_exists selected value
    exact ⟨⟨updated⟩, .intro (.intro selected) written⟩

theorem ordinary_completed {environment : Environment} {store finalStore : Store}
    {index target : Nat} {type : Ty} {reason : Word} {value optional : Value}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType type) target))
    (read : store.read? target = some optional)
    (evaluated : Evaluates environment store (OptionalCell.read type (.var index) reason) value finalStore) :
    (∃ annotation payload, optional = .inRight annotation payload ∧ value = .inRight .word payload ∧ finalStore = store) ∨
    (∃ annotation payload, optional = .inLeft annotation payload ∧ value = .inLeft type (.word reason) ∧ finalStore = store) := by
  cases evaluated with
  | caseLeft loaded branch =>
    cases loaded with
    | loadCell reference actualRead =>
      cases reference with
      | var actualLookup =>
        have same := Option.some.inj (lookup.symm.trans actualLookup)
        cases same
        have same := Option.some.inj (read.symm.trans actualRead)
        cases branch with
        | inLeft token =>
          cases token
          exact .inr ⟨_, _, same, rfl, rfl⟩
  | caseRight loaded branch =>
    cases loaded with
    | loadCell reference actualRead =>
      cases reference with
      | var actualLookup =>
        have same := Option.some.inj (lookup.symm.trans actualLookup)
        cases same
        have same := Option.some.inj (read.symm.trans actualRead)
        cases branch with
        | inRight payload =>
          cases payload with
          | var samePayload =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at samePayload
            cases samePayload
            exact .inl ⟨_, _, same, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCompletion

namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleExpressionReadCompletion

/-- Mapping completion constructs only the actual raw source rule and its full
heap relation; callers choose their ordinary or staged outer constructor. -/
theorem Certificate.mapping_completed {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    (declaredMapping : ∃ key value, certificate.declared.scheme.body = .mapping key value)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep}
    {result : Value} {finalStore : Store} (evaluation : Evaluates actual store (code.rename ξ) result finalStore) :
    ∃ sourceValue after,
      Dynamic.ExpressionFormEvaluates program sourceContext evidence source environment heap
        certificate.node.form [] [] sourceValue after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults (.value sourceValue) result ∧
      CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
  rcases certificate with ⟨node, type, binder, name, declared, index, metadata, form, binderOwner, slot, declaration, emitted⟩
  rcases binding with ⟨declaredScope, occurrence⟩
  dsimp only at *
  obtain ⟨location, cell, lookup, read, cellType, _⟩ := locals.lookup declaredScope
  obtain ⟨target, selected, optional, nativeLookup, reference, selectedRead, nativeRead, represented⟩ :=
    GenericHeap.lookup_visible environments heaps lookup slot
  have sameCell := read.functional selectedRead
  subst selected
  cases emitted with
  | ordinary notMapping => exact False.elim (notMapping declaredMapping)
  | @mapping key value literal declaredType generated =>
    obtain ⟨empty, encodedType, quoted, emptyRep⟩ := generated.represents functions extension (.mapping .empty) mapping world
    rw [mapping_rename quoted] at evaluation
    have completed := read_completed (agrees nativeLookup) nativeRead quoted evaluation
    cases represented with
    | initialized payload =>
      dsimp only at cellType
      rcases completed with ⟨_, _, sameOptional, sameValue, sameStore⟩ | ⟨_, _, impossible, _⟩
      · cases sameOptional
        subst result finalStore
        exact ⟨_, heap, form ▸ .local rfl lookup read rfl rfl,
          .value (.compatible (by simpa only [← cellType] using occurrence) payload), heaps, .refl _ _, .refl _⟩
      · cases impossible
    | @uninitialized sourceType _ projected =>
      change sourceType = declared.scheme.body at cellType
      have same : encodedType = type := Except.ok.inj (emptyRep.projection.symm.trans (cellType ▸ projected))
      subst encodedType
      rcases completed with ⟨_, _, impossible, _⟩ | ⟨_, _, sameOptional, sameValue, originalWritten⟩
      · cases impossible
      · cases sameOptional
        subst result
        obtain ⟨after, written⟩ := writes_exists read (.mapping _ _ [])
        have cellPayload : ValueRep context.checked registry functions mapping world sourceType (.mapping _ _ []) empty type :=
          cellType.symm ▸ emptyRep
        obtain ⟨updated, nativeWritten, finalHeaps, frame⟩ := heaps.write_initialized reference read cellPayload written
        have sameStore := Option.some.inj (nativeWritten.symm.trans originalWritten)
        cases sameStore
        exact ⟨_, after, form ▸ .localEmptyMapping rfl lookup read rfl (cellType.trans declaredType) rfl written,
          .value (.compatible (cellType ▸ occurrence) cellPayload), finalHeaps, frame, .of_write written⟩

/-- Every completed accepted local read determines its independent source outcome. -/
theorem Certificate.completed_with_diagnostics {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep} (uninitialized : UninitializedPolicy certificate sourceContext environment heap faults)
    {value : Value} {finalStore : Store} (evaluation : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after,
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
  by_cases declaredMapping : ∃ key value, certificate.declared.scheme.body = .mapping key value
  · obtain ⟨sourceValue, after, raw, represented, finalHeaps, frame, metadata⟩ :=
      certificate.mapping_completed functions extension program sourceContext evidence binding declaredMapping
        environments heaps locals agrees evaluation
    refine ⟨.value sourceValue, after, .value (.intro (middle := after) (raw := sourceValue) (lookupExpression?_sound certificate.metadata.found) ?_ ?_),
      represented, finalHeaps, frame, metadata⟩
    · simpa only [certificate.metadata.requirements, certificate.metadata.coercions] using raw
    · rw [certificate.metadata.coercions]; exact .nil
  · rcases certificate with ⟨node, type, binder, name, declared, index, metadata, form, binderOwner, slot, declaration, emitted⟩
    rcases binding with ⟨declaredScope, occurrence⟩
    dsimp only at *
    cases emitted with
    | mapping declaredType generated => exact False.elim (declaredMapping ⟨_, _, declaredType⟩)
    | ordinary _ =>
      obtain ⟨location, cell, lookup, read, cellType, _⟩ := locals.lookup declaredScope
      obtain ⟨target, selected, optional, nativeLookup, reference, selectedRead, nativeRead, represented⟩ :=
        GenericHeap.lookup_visible environments heaps lookup slot
      have sameCell := read.functional selectedRead
      subst selected
      have ordinary := represented.ordinary
      have result := ordinary_completed (agrees nativeLookup) nativeRead evaluation
      have contains := lookupExpression?_sound metadata.found
      cases represented with
      | @initialized sourceType _ sourceValue nativeValue payload =>
        dsimp only at cellType
        rcases result with ⟨_, native, sameOptional, sameValue, sameStore⟩ | ⟨_, _, impossible, _⟩
        · cases sameOptional
          subst value finalStore
          refine ⟨.value _, heap, .value (.intro (middle := heap) (raw := sourceValue) contains ?_ ?_),
            .value (.compatible (by simpa only [← cellType] using occurrence) payload), heaps, .refl _ _, .refl _⟩
          · rw [form, metadata.requirements, metadata.coercions]
            exact .local rfl lookup read ordinary rfl
          · rw [metadata.coercions]; exact .nil
        · cases impossible
      | uninitialized projected =>
        dsimp only at cellType
        rcases result with ⟨_, _, impossible, _⟩ | ⟨_, _, _, sameValue, sameStore⟩
        · cases impossible
        · subst value finalStore
          refine ⟨.fault (.uninitializedLocation location), heap, .fault (.form contains ?_),
            .fault (uninitialized location _ ⟨contains, form, declaredScope, occurrence, lookup, read,
              cellType, ordinary, rfl, by simpa only [cellType] using declaredMapping⟩), heaps, .refl _ _, .refl _⟩
          rw [form, metadata.requirements, metadata.coercions]
          exact .localUninitialized (owned := []) rfl lookup read ordinary rfl (by simpa only [cellType] using declaredMapping)

/-- The original uniform inclusion supplies the policy at its actual witness. -/
theorem Certificate.completed {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep} (uninitialized : ∀ location, faults (.uninitializedLocation location) reason)
    {value : Value} {finalStore : Store} (evaluation : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after,
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
  exact certificate.completed_with_diagnostics functions extension program sourceContext evidence binding
    environments heaps locals agrees (fun location _ _ => uninitialized location) evaluation

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadSource
/-! Local uniqueness of independent ordinary source reads, including lazy
mapping initialization. This uses their actual source derivations and readable
ordinary cell, and makes no whole-language determinism assumption. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
open Frontend SourceInference

private theorem contains_unique {source : TypedSource} {id : ExpressionId} {left right : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (first : ContainsExpression source id left)
    (second : ContainsExpression source id right) : left = right :=
  Option.some.inj ((lookupExpression?_complete unique first).symm.trans (lookupExpression?_complete unique second))

private theorem cellsWrite_unique {cells left right : List Dynamic.Cell} {index : Nat} {value : Dynamic.Cell}
    (first : Dynamic.Heap.CellsWrite cells index value left)
    (second : Dynamic.Heap.CellsWrite cells index value right) : left = right := by
  induction first generalizing right with
  | head => cases second; rfl
  | tail _ ih => cases second with | tail second => exact congrArg (_ :: ·) (ih second)

private theorem writes_unique {before left right : Dynamic.Heap} {location : Dynamic.Location} {value : Option Dynamic.Value}
    (first : Dynamic.Heap.Writes before location value left)
    (second : Dynamic.Heap.Writes before location value right) : left = right := by
  cases first with
  | intro firstRead firstWrite =>
    cases second with
    | intro secondRead secondWrite =>
      have same := firstRead.functional secondRead
      cases same
      cases cellsWrite_unique firstWrite secondWrite
      rfl

private inductive ReadResult (heap : Dynamic.Heap) (location : Dynamic.Location) (cell : Dynamic.Cell) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | initialized {value} (stored : cell.value = some value) : ReadResult heap location cell (.value value) heap
  | mapping {key value after} (type : cell.type = .mapping key value) (empty : cell.value = none)
      (written : Dynamic.Heap.Writes heap location (some (.mapping key value [])) after) :
      ReadResult heap location cell (.value (.mapping key value [])) after
  | uninitialized (empty : cell.value = none) (notMapping : ¬ ∃ key value, cell.type = .mapping key value) :
      ReadResult heap location cell (.fault (.uninitializedLocation location)) heap

private theorem ReadResult.unique {heap firstHeap secondHeap : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell}
    {first second : Dynamic.ExpressionOutcome} (left : ReadResult heap location cell first firstHeap)
    (right : ReadResult heap location cell second secondHeap) : first = second ∧ firstHeap = secondHeap := by
  cases left with
  | initialized stored =>
    cases right with
    | initialized other => cases Option.some.inj (stored.symm.trans other); exact ⟨rfl, rfl⟩
    | mapping _ empty _ | uninitialized empty _ => rw [stored] at empty; cases empty
  | mapping type empty written =>
    cases right with
    | initialized stored => rw [empty] at stored; cases stored
    | mapping other _ secondWrite =>
      obtain ⟨rfl, rfl⟩ := TypeSystem.Ty.mapping.inj (type.symm.trans other)
      exact ⟨rfl, writes_unique written secondWrite⟩
    | uninitialized _ notMapping => exact False.elim (notMapping ⟨_, _, type⟩)
  | uninitialized empty notMapping =>
    cases right with
    | initialized stored => rw [empty] at stored; cases stored
    | mapping type _ _ => exact False.elim (notMapping ⟨_, _, type⟩)
    | uninitialized => exact ⟨rfl, rfl⟩

private theorem result_of_trace {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap after : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    {location : Dynamic.Location} {cell : Dynamic.Cell} {outcome : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (form : node.form = .reference name (.local binder)) (coercions : node.coercions = [])
    (lookup : Dynamic.Environment.LooksUp environment binder location) (read : Dynamic.Heap.Reads heap location cell)
    (ordinary : cell.generalized = none)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id outcome after) :
    ReadResult heap location cell outcome after := by
  have align : ∀ {otherLocation otherCell},
      Dynamic.Environment.LooksUp environment binder otherLocation → Dynamic.Heap.Reads heap otherLocation otherCell →
      otherLocation = location ∧ otherCell = cell := by
    intro otherLocation otherCell otherLookup otherRead
    have sameLocation := otherLookup.functional lookup
    subst otherLocation
    exact ⟨rfl, otherRead.functional read⟩
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro otherContains raw path =>
      have same := contains_unique unique otherContains contains
      subst_vars
      rw [coercions] at path
      cases path
      rw [form] at raw
      cases raw with
      | «local» _ otherLookup otherRead _ initialized =>
        obtain ⟨rfl, rfl⟩ := align otherLookup otherRead
        exact .initialized initialized
      | localEmptyMapping _ otherLookup otherRead _ type empty written =>
        obtain ⟨rfl, rfl⟩ := align otherLookup otherRead
        exact .mapping type empty written
    | generalizedLocal otherContains otherForm _ otherLookup otherRead descriptor _ _ _ =>
      have same := contains_unique unique otherContains contains
      subst_vars
      rw [form] at otherForm
      cases otherForm
      obtain ⟨rfl, rfl⟩ := align otherLookup otherRead
      rw [ordinary] at descriptor
      cases descriptor
  | fault failed =>
    cases failed with
    | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
    | form otherContains raw =>
      have same := contains_unique unique otherContains contains
      subst_vars
      rw [form] at raw
      cases raw with
      | localUnbound _ unbound => exact False.elim (unbound.excludes_lookup lookup)
      | localDangling _ otherLookup dangling =>
        have same := otherLookup.functional lookup
        subst_vars
        exact False.elim (dangling.excludes_read read)
      | localUninitialized _ otherLookup otherRead _ empty notMapping =>
        obtain ⟨rfl, rfl⟩ := align otherLookup otherRead
        exact .uninitialized empty notMapping
    | coercion otherContains _ failed =>
      have same := contains_unique unique otherContains contains
      subst_vars
      rw [coercions] at failed
      cases failed
    | generalizedLocalRequirement otherContains otherForm _ otherLookup otherRead descriptor _ _ _
    | generalizedLocalCoercion otherContains otherForm _ otherLookup otherRead descriptor _ _ _ =>
      have same := contains_unique unique otherContains contains
      subst_vars
      rw [form] at otherForm
      cases otherForm
      obtain ⟨rfl, rfl⟩ := align otherLookup otherRead
      rw [ordinary] at descriptor
      cases descriptor

/-- This uniqueness statement is restricted to a readable ordinary local.
Generalized closure instantiation and arbitrary source calls are not included. -/
theorem source_outcome_unique {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap firstHeap secondHeap : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    {location : Dynamic.Location} {cell : Dynamic.Cell} {first second : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (form : node.form = .reference name (.local binder)) (coercions : node.coercions = [])
    (lookup : Dynamic.Environment.LooksUp environment binder location) (read : Dynamic.Heap.Reads heap location cell)
    (ordinary : cell.generalized = none)
    (left : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id first firstHeap)
    (right : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id second secondHeap) :
    first = second ∧ firstHeap = secondHeap :=
  (result_of_trace unique contains form coercions lookup read ordinary left).unique
    (result_of_trace unique contains form coercions lookup read ordinary right)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadMeaning
/-! Bidirectional source correspondence for accepted compatible local reads.
The independent source trace supplies only the forward direction; every
completed Core execution reconstructs a source trace in the reverse direction.
All child evaluation is derived, including lazy mapping initialization. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

theorem Certificate.preserves {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep} (uninitialized : ∀ location, faults (.uninitializedLocation location) reason)
    (unique : NodeOccurrencesUnique source)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after) :
    ∃ value finalStore,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
  obtain ⟨actualOutcome, actualHeap, value, finalStore, sourceTrace, evaluated, represented, finalHeaps, frame, metadata⟩ :=
    certificate.evaluates functions extension program sourceContext evidence binding environments heaps locals agrees uninitialized
  obtain ⟨location, cell, lookup, read, _, _⟩ := locals.lookup binding.declared
  obtain ⟨_, selected, _, _, _, selectedRead, _, cellRep⟩ :=
    GenericHeap.lookup_visible environments heaps lookup certificate.slot
  have sameCell := read.functional selectedRead
  subst selected
  obtain ⟨rfl, rfl⟩ := source_outcome_unique unique (lookupExpression?_sound certificate.metadata.found)
    certificate.form certificate.metadata.coercions lookup read cellRep.ordinary sourceTrace trace
  exact ⟨value, finalStore, evaluated, represented, finalHeaps, frame, metadata⟩

theorem Certificate.reflects {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep} (uninitialized : ∀ location, faults (.uninitializedLocation location) reason)
    {value : Value} {finalStore : Store} (evaluation : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after,
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
  exact certificate.completed functions extension program sourceContext evidence binding
    environments heaps locals agrees uninitialized evaluation

/-- A static occurrence receipt for the universal child-expression interface.
The receipt contains compiler and source typing facts, never a child run. -/
def LoweredRead (fuel : Nat) (context : ValuesContext) (source : TypedSource)
    (sourceContext : SourceSemantics.Context) (reasonAt : ExpressionId → Word) :
    GenericExpressionMeaning.Certificate := fun scope id lowered =>
  ∃ certificate : Certificate fuel context source scope id (reasonAt id) lowered.expression,
    certificate.type = lowered.type ∧ StaticBinding certificate sourceContext

/-- Lexical declarations are checked independently of native projection. Only
binders actually visible in the compiler scope are required in this context. -/
def ScopeDeclarations (source : TypedSource) (scope : Scope) (context : SourceSemantics.Context) : Prop :=
  ∀ binder declared index type,
    SourceCoreLocalCell.lookup? scope binder = some (index, type) →
    SourceCoreDataPlaces.rootBinder source binder = .ok declared →
    Resolved.LocalScope.Lookup context.locals binder declared.scheme

theorem loweredRead_of_accepted {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {sourceContext : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (accepted : SourceCoreCompatibleDataExpressions.lowerRead fuel context source scope id (reasonAt id) = .ok lowered.expression)
    (read : SourceCoreCompatibleDataExpressions.readExpression context.checked source id = .ok (node, lowered.type))
    (unique : NodeOccurrencesUnique source)
    (declarations : ScopeDeclarations source scope sourceContext)
    (typed : ExpressionHasType source sourceContext id node.type) :
    LoweredRead fuel context source sourceContext reasonAt scope id lowered := by
  obtain ⟨certificate⟩ := of_accepted accepted
  have metadata := metadata_of_read read
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans metadata.found)
  have projection := certificate.metadata.projected
  rw [nodeEq] at projection
  have typeEq := Except.ok.inj (projection.symm.trans metadata.projected)
  refine ⟨certificate, typeEq, StaticBinding.of_expression_type certificate unique
    (declarations _ _ _ _ certificate.slot certificate.declaration) ?_⟩
  simpa only [nodeEq] using typed

/-- The forward universal interface is discharged for every certified read. -/
theorem loweredRead_preserves {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (reasonAt : ExpressionId → Word) {faults : FunctionCalls.FaultRep}
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (unique : NodeOccurrencesUnique source) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel context.checked registry functions)
      program sourceContext evidence source (LoweredRead fuel context source sourceContext reasonAt) faults := by
  intro scope id lowered receipt node found mapping world administrative environment canonical actual before store ξ outcome after
    environments heaps locals agrees trace
  obtain ⟨certificate, typeEq, binding⟩ := receipt
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans found)
  obtain ⟨value, finalStore, evaluated, represented, finalHeaps, frame, metadata⟩ :=
    certificate.preserves functions extension program sourceContext evidence binding environments heaps locals agrees
      (uninitialized id) unique trace
  refine ⟨value, finalStore, mapping, world, evaluated, ?_, finalHeaps, .refl _, .refl _, frame, metadata⟩
  simpa only [nodeEq, typeEq] using represented

/-- Every completed Core read reconstructs its finite source outcome. -/
theorem loweredRead_reflects {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (reasonAt : ExpressionId → Word) {faults : FunctionCalls.FaultRep}
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id)) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel context.checked registry functions)
      program sourceContext evidence source (LoweredRead fuel context source sourceContext reasonAt) faults := by
  intro scope id lowered receipt node found mapping world administrative environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluation
  obtain ⟨certificate, typeEq, binding⟩ := receipt
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans found)
  obtain ⟨outcome, after, sourceTrace, represented, finalHeaps, frame, metadata⟩ :=
    certificate.reflects functions extension program sourceContext evidence binding environments heaps locals agrees
      (uninitialized id) evaluation
  refine ⟨outcome, after, mapping, world, sourceTrace, ?_, finalHeaps, .refl _, .refl _, frame, metadata⟩
  simpa only [nodeEq, typeEq] using represented

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProductTree
/-! A finite static fragment for literal/read/group/binary-tuple expressions.
The native code is indexed by the exact compiled child expressions. Product
metadata is related through independent source typing, never native projection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProducts
open Core Frontend SourceInference
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope
abbrev Metadata := CompatibleExpressionReads.Metadata

/-- A syntactic restriction on the reached source subtree. It contains no
compiler results, runtime traces, or semantic child hypotheses. -/
inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | literal {id node} (found : source.lookupExpression? id = some node)
      (atomic : CompatibleExpressionLiterals.Atomic node.form) : Syntax source id
  | read {id node name binder} (found : source.lookupExpression? id = some node)
      (form : node.form = .reference name (.local binder)) : Syntax source id
  | group {id node inner} (found : source.lookupExpression? id = some node)
      (form : node.form = .group inner) (child : Syntax source inner) : Syntax source id
  | pair {id node left right} (found : source.lookupExpression? id = some node)
      (form : node.form = .tuple [left, right])
      (first : Syntax source left) (second : Syntax source right) : Syntax source id

/-- The leaves are the already authenticated literal/read receipts. The
compound rows record independent source type equality and exact child code. -/
inductive Tree (fuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | literal {id lowered} (receipt : CompatibleExpressionLiterals.Certificate solved source id lowered) :
      Tree fuel values source context solved reasonAt scope id lowered
  | read {id lowered} (receipt : CompatibleExpressionReads.LoweredRead fuel values source context reasonAt scope id lowered) :
      Tree fuel values source context solved reasonAt scope id lowered
  | group {id node inner innerNode lowered}
      (metadata : Metadata values.checked source id node lowered.type)
      (form : node.form = .group inner)
      (innerFound : source.lookupExpression? inner = some innerNode)
      (sourceType : node.type = innerNode.type)
      (child : Tree fuel values source context solved reasonAt scope inner lowered) :
      Tree fuel values source context solved reasonAt scope id lowered
  | pair {id node left right leftNode rightNode first second}
      (metadata : Metadata values.checked source id node (.product first.type second.type))
      (form : node.form = .tuple [left, right])
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (sourceType : node.type = .product leftNode.type rightNode.type)
      (firstTree : Tree fuel values source context solved reasonAt scope left first)
      (secondTree : Tree fuel values source context solved reasonAt scope right second) :
      Tree fuel values source context solved reasonAt scope id
        ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩

private theorem contains_node {source : TypedSource} {id : ExpressionId} {node other : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (contains : ContainsExpression source id other) : other = node :=
  Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)

/-- Group raw type equality is recovered from the independent typing rule and
its empty output coercion path. -/
theorem group_source_types {source : TypedSource} {context : SourceSemantics.Context}
    {id inner : ExpressionId} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .group inner) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    ∃ innerNode, source.lookupExpression? inner = some innerNode ∧ node.type = innerNode.type ∧
      ExpressionHasType source context inner innerNode.type := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ requirements =>
    have same := contains_node unique found contains
    subst actualNode
    have path := requirements.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    cases raw with
    | group child =>
      obtain ⟨innerNode, contained, sameType⟩ := child.stored_type
      exact ⟨innerNode, lookupExpression?_complete unique contained, sameType.symm, sameType ▸ child⟩

/-- Binary tuple source metadata follows `ExpressionsHaveTypes`; no equality
between projected native types is used to identify raw element types. -/
theorem pair_source_types {source : TypedSource} {context : SourceSemantics.Context}
    {id left right : ExpressionId} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .tuple [left, right]) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    ∃ leftNode rightNode, source.lookupExpression? left = some leftNode ∧
      source.lookupExpression? right = some rightNode ∧ node.type = .product leftNode.type rightNode.type ∧
      ExpressionHasType source context left leftNode.type ∧ ExpressionHasType source context right rightNode.type := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ requirements =>
    have same := contains_node unique found contains
    subst actualNode
    have path := requirements.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize rawTypeEq : node.type = rawType at raw
    cases raw with
    | tuple elements =>
      cases elements with
      | cons first rest =>
        cases rest with
        | cons second rest =>
          cases rest
          obtain ⟨leftNode, leftContained, leftType⟩ := first.stored_type
          obtain ⟨rightNode, rightContained, rightType⟩ := second.stored_type
          refine ⟨leftNode, rightNode, lookupExpression?_complete unique leftContained,
            lookupExpression?_complete unique rightContained, ?_, leftType ▸ first, rightType ▸ second⟩
          simp only [TypeSystem.Ty.productMany, ← leftType, ← rightType]

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProducts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProductSource
/-! Independent source composition/inversion for empty-coercion groups and
binary tuples. Evaluation order and the faulting prefix remain explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProducts
open Core Frontend SourceInference

private theorem contains_unique {source : TypedSource} {id : ExpressionId} {left right : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (first : ContainsExpression source id left)
    (second : ContainsExpression source id right) : left = right :=
  Option.some.inj ((lookupExpression?_complete unique first).symm.trans (lookupExpression?_complete unique second))

private theorem evaluation_raw
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder)) (empty : node.coercions = [])
    (evaluation : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    Dynamic.ExpressionFormEvaluates program context evidence source environment before node.form node.requirements node.coercions value after := by
  cases evaluation with
  | intro found raw coercions =>
    have same := contains_unique unique found contains
    subst same
    rw [empty] at coercions
    cases coercions
    exact raw
  | generalizedLocal found form _ _ _ _ _ _ _ =>
    have same := contains_unique unique found contains
    subst same
    exact False.elim (notLocal _ _ form)

private theorem fault_raw
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder)) (empty : node.coercions = [])
    (fault : Dynamic.ExpressionFaults program context evidence source environment before id reason after) :
    Dynamic.ExpressionFormFaults program context evidence source environment before node.form node.requirements node.coercions reason after := by
  cases fault with
  | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
  | form found raw => exact contains_unique unique found contains ▸ raw
  | coercion found _ failed =>
    have same := contains_unique unique found contains
    subst same
    rw [empty] at failed
    cases failed
  | generalizedLocalRequirement found form _ _ _ _ _ _ _ | generalizedLocalCoercion found form _ _ _ _ _ _ _ =>
    have same := contains_unique unique found contains
    subst same
    exact False.elim (notLocal _ _ form)

variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id : ExpressionId}
  {node : ExpressionNode} {type : Ty} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {outcome : Dynamic.ExpressionOutcome}

theorem group_inv (metadata : Metadata checked source id node type) {inner : ExpressionId}
    (form : node.form = .group inner) (unique : NodeOccurrencesUnique source)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before inner outcome after := by
  cases trace with
  | value evaluated =>
    have raw := evaluation_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form] at raw
    cases raw with | group _ child => exact .value child
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form] at raw
    cases raw with | group _ child => exact .fault child

theorem group_intro (metadata : Metadata checked source id node type) {inner : ExpressionId}
    (form : node.form = .group inner)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before inner outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases trace with
  | value evaluated =>
    apply Dynamic.ExpressionEvaluatesOutcome.value
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
    · rw [form, metadata.requirements, metadata.coercions]; exact .group rfl evaluated
    · rw [metadata.coercions]; exact .nil
  | fault failed =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .group rfl failed

inductive PacksOutcome : DataExpressionSequence.Outcome → Dynamic.ExpressionOutcome → Prop where
  | values {values packed} (pack : Dynamic.ValuesPack values packed) : PacksOutcome (.ok values) (.value packed)
  | fault (reason : Dynamic.SemanticFault) : PacksOutcome (.error reason) (.fault reason)

theorem PacksOutcome.functional {input left right} (first : PacksOutcome input left) (second : PacksOutcome input right) : left = right := by
  cases first with
  | values first => cases second with | values second => exact congrArg _ (first.functional second)
  | fault => cases second; rfl

theorem pair_inv (metadata : Metadata checked source id node type) {left right : ExpressionId}
    (form : node.form = .tuple [left, right]) (unique : NodeOccurrencesUnique source)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    ∃ sequence, DataExpressionSequence.Trace program context evidence source environment before [left, right] sequence after ∧
      PacksOutcome sequence outcome := by
  cases trace with
  | value evaluated =>
    have raw := evaluation_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form] at raw
    cases raw with | tuple _ children pack => exact ⟨_, .values children, .values pack⟩
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form] at raw
    cases raw with | tuple _ children => exact ⟨_, .fault children, .fault _⟩

theorem pair_intro (metadata : Metadata checked source id node type) {left right : ExpressionId}
    (form : node.form = .tuple [left, right]) {sequence : DataExpressionSequence.Outcome}
    (trace : DataExpressionSequence.Trace program context evidence source environment before [left, right] sequence after)
    (packed : PacksOutcome sequence outcome) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases packed with
  | values pack =>
    cases trace with
    | values evaluated =>
      apply Dynamic.ExpressionEvaluatesOutcome.value
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
      · rw [form, metadata.requirements, metadata.coercions]; exact .tuple rfl evaluated pack
      · rw [metadata.coercions]; exact .nil
  | fault reason =>
    cases trace with
    | fault failed =>
      apply Dynamic.ExpressionEvaluatesOutcome.fault
      apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
      rw [form, metadata.requirements, metadata.coercions]
      exact .tuple rfl failed

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProducts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexSourceReceipts
/-! Index receipts retain each actual issuer and the original ordered lookup.
Their source membership is unconditional; canonical source association is a
separate finite receipt. These definitions perform no preparation or evaluation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexSourceReceipts
open Core Frontend SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
abbrev IndexSite := SourceCoreDataFaultSites.IndexSite

def Selected (indices : List IndexSite) (owner : Key) (id : ExpressionId) : Prop :=
  ∃ site, indices.find? (fun site => decide (site.owner = owner ∧ site.expression = id)) = some site

def Origin (sources : List (Key × TypedSource)) (site : IndexSite) : Prop :=
  ∃ source node base key,
    (site.owner, source) ∈ sources ∧ source.owner = site.owner.declaration ∧
    SourceSemantics.ContainsExpression source site.expression node ∧ node.form = .index base key ∧
    site.diagnostic = ⟨.typeMismatch node.type none, .occurrence node.id.occurrence, some node.span⟩

def NodesCovered (owner : Key) (nodes : List Node) (indices : List IndexSite) : Prop :=
  ∀ node, Node.expression node ∈ nodes → ∀ base key, node.form = .index base key →
    Selected indices owner node.id

def SourcesCovered (sources : List (Key × TypedSource)) (indices : List IndexSite) : Prop :=
  ∀ owner source, (owner, source) ∈ sources → NodesCovered owner source.nodes indices

def NodeSelected (owner : Key) (retained : Node) (indices : List IndexSite) : Prop :=
  ∀ node, retained = .expression node → ∀ base key, node.form = .index base key →
    Selected indices owner node.id

structure Inventory (sources visited : List (Key × TypedSource)) (indices : List IndexSite) : Prop where
  origins : ∀ site, site ∈ indices → Origin sources site
  unique : (indices.map (fun site => (site.owner, site.expression))).Nodup
  covered : SourcesCovered visited indices

structure NodeInventory (sources visited : List (Key × TypedSource))
    (owner : Key) (seen : List Node) (indices : List IndexSite) : Prop where
  inventory : Inventory sources visited indices
  covered : NodesCovered owner seen indices

theorem Inventory.empty (sources : List (Key × TypedSource)) : Inventory sources [] [] := by
  refine ⟨?_, by simp, ?_⟩
  · intro site member
    cases member
  · intro owner source member
    cases member

theorem Selected.append {indices : List IndexSite} {owner : Key} {id : ExpressionId}
    (selected : Selected indices owner id) (later : List IndexSite) : Selected (indices ++ later) owner id := by
  obtain ⟨site, found⟩ := selected
  exact ⟨site, by simp only [List.find?_append, found]; rfl⟩

theorem NodesCovered.append_indices {owner : Key} {nodes : List Node} {indices : List IndexSite}
    (covered : NodesCovered owner nodes indices) (later : List IndexSite) :
    NodesCovered owner nodes (indices ++ later) := by
  intro node member base key form
  exact (covered node member base key form).append later

theorem NodesCovered.step {owner : Key} {seen : List Node} {retained : Node} {indices : List IndexSite}
    (covered : NodesCovered owner seen indices) (selected : NodeSelected owner retained indices) :
    NodesCovered owner (seen ++ [retained]) indices := by
  intro node member base key form
  rcases List.mem_append.mp member with old | current
  · exact covered node old base key form
  · exact selected node (List.mem_singleton.mp current).symm base key form

theorem NodeSelected.statement (owner : Key) (node : StatementNode) (indices : List IndexSite) :
    NodeSelected owner (.statement node) indices := by
  intro expression same
  cases same

theorem NodeInventory.start {sources visited : List (Key × TypedSource)} {indices : List IndexSite}
    (inventory : Inventory sources visited indices) (owner : Key) :
    NodeInventory sources visited owner [] indices := by
  refine ⟨inventory, ?_⟩
  intro node member
  cases member

theorem NodeInventory.step {sources visited : List (Key × TypedSource)} {owner : Key}
    {seen : List Node} {indices : List IndexSite} {retained : Node}
    (inventory : NodeInventory sources visited owner seen indices)
    (selected : NodeSelected owner retained indices) :
    NodeInventory sources visited owner (seen ++ [retained]) indices :=
  ⟨inventory.inventory, inventory.covered.step selected⟩

theorem NodeInventory.finish {sources visited : List (Key × TypedSource)} {owner : Key}
    {source : TypedSource} {indices : List IndexSite}
    (inventory : NodeInventory sources visited owner source.nodes indices) :
    Inventory sources (visited ++ [(owner, source)]) indices := by
  refine ⟨inventory.inventory.origins, inventory.inventory.unique, ?_⟩
  intro key actual member
  rcases List.mem_append.mp member with old | current
  · exact inventory.inventory.covered key actual old
  · cases List.mem_singleton.mp current
    exact inventory.covered

theorem Inventory.append_index {sources visited : List (Key × TypedSource)} {indices : List IndexSite}
    (inventory : Inventory sources visited indices) {owner : Key} {source : TypedSource} {node : ExpressionNode}
    {base key : ExpressionId} (member : (owner, source) ∈ sources) (owns : source.owner = owner.declaration)
    (contains : SourceSemantics.ContainsExpression source node.id node) (form : node.form = .index base key)
    (absent : indices.find? (fun site => decide (site.owner = owner ∧ site.expression = node.id)) = none)
    (reason : Word) :
    Inventory sources visited (indices ++ [⟨owner, node.id, reason,
      ⟨.typeMismatch node.type none, .occurrence node.id.occurrence, some node.span⟩⟩]) := by
  refine ⟨?_, ?_, ?_⟩
  · intro site occurs
    rcases List.mem_append.mp occurs with old | current
    · exact inventory.origins site old
    · cases List.mem_singleton.mp current
      exact ⟨source, node, base, key, member, owns, contains, form, rfl⟩
  · rw [List.map_append]
    apply List.nodup_append.mpr
    refine ⟨inventory.unique, by simp, ?_⟩
    intro pair pairMember other otherMember same
    obtain ⟨site, siteMember, pairEq⟩ := List.mem_map.mp pairMember
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at otherMember
    have pairSame := same.trans otherMember
    have hit : site.owner = owner ∧ site.expression = node.id := by
      exact Prod.mk.inj (pairEq.trans pairSame)
    have avoids := List.find?_eq_none.mp absent site siteMember
    exact avoids (by simp [hit.1, hit.2])
  · intro key actual occurs
    exact (inventory.covered key actual occurs).append_indices _

theorem selected_fresh {indices : List IndexSite} {owner : Key} {node : ExpressionNode} (reason : Word)
    (absent : indices.find? (fun site => decide (site.owner = owner ∧ site.expression = node.id)) = none) :
    Selected (indices ++ [⟨owner, node.id, reason,
      ⟨.typeMismatch node.type none, .occurrence node.id.occurrence, some node.span⟩⟩]) owner node.id := by
  refine ⟨⟨owner, node.id, reason,
    ⟨.typeMismatch node.type none, .occurrence node.id.occurrence, some node.span⟩⟩, ?_⟩
  rw [List.find?_append, absent]
  simp

theorem NodeInventory.append_index {sources visited : List (Key × TypedSource)} {owner : Key}
    {seen : List Node} {indices : List IndexSite} {source : TypedSource} {node : ExpressionNode}
    {base key : ExpressionId} (inventory : NodeInventory sources visited owner seen indices)
    (member : (owner, source) ∈ sources) (owns : source.owner = owner.declaration)
    (contains : SourceSemantics.ContainsExpression source node.id node) (form : node.form = .index base key)
    (absent : indices.find? (fun site => decide (site.owner = owner ∧ site.expression = node.id)) = none)
    (reason : Word) :
    NodeInventory sources visited owner (seen ++ [.expression node])
      (indices ++ [⟨owner, node.id, reason,
        ⟨.typeMismatch node.type none, .occurrence node.id.occurrence, some node.span⟩⟩]) := by
  refine ⟨inventory.inventory.append_index member owns contains form absent reason, ?_⟩
  apply (inventory.covered.append_indices _).step
  intro actual same base key actualForm
  cases same
  exact selected_fresh reason absent

def Receipt {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    (plan : SourceSpecializationWorklist.Plan) (root : Key) (sources : List (Key × TypedSource))
    (program : SourceCoreCompatibleDataPlaceFaultSites.Program context) : Prop :=
  CompatiblePlaceMissingReservedReceipts.ReservedReceipt context plan root program ∧
    Inventory (plan.specializations.map (fun row => (row.key, row.function.typedBody)) ++ sources)
      (plan.specializations.map (fun row => (row.key, row.function.typedBody)) ++ sources)
      program.program.expressions.indices

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexSourceReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadNativeTyping
/-! Successful checked reads supply the native type facts needed by the
ordinary cell and lazy mapping branches. Quoted data uses the actual encoder
typing together with checked projection; runtime value typing alone does not
authenticate the annotations on unused sum branches. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
open Core Frontend SourceInference
open CompatibleMapping.VirtualRoot

/-- The checked projection retains native well-formedness under its actual
catalog. A raw projection equation alone does not supply this fact. -/
theorem projectType_wellFormed {checked : SourceCoreCompatibleCatalog.Checked}
    {site : SourceCoreElaboration.ErrorSite} {sourceType : TypeSystem.Ty} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.projectType checked site sourceType = .ok type) :
    type.WellFormed checked.catalog.definitions := by
  unfold SourceCoreCompatibleDataExpressions.projectType at accepted
  cases projected : checked.project sourceType with
  | error error => simp [projected, Except.map, Except.mapError] at accepted
  | ok projection =>
    simp only [projected, Except.map, Except.mapError, Except.ok.injEq] at accepted
    subst type
    exact projection.typed

theorem readExpression_wellFormed {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : ExpressionId} {node : ExpressionNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readExpression checked source id = .ok (node, type)) :
    type.WellFormed checked.catalog.definitions := by
  have metadata := metadata_of_read accepted
  rw [SourceCoreCompatibleDataExpressions.readExpression, if_neg (not_not_intro metadata.owner), metadata.found]
    at accepted
  simp only [metadata.requirements, metadata.coercions, List.isEmpty_nil,
    pure, Except.pure, bind, Except.bind] at accepted
  cases projected : SourceCoreCompatibleDataExpressions.projectType checked (.occurrence id.occurrence) node.type with
  | error error => simp [projected] at accepted
  | ok native =>
    simp only [projected] at accepted
    cases accepted
    exact projectType_wellFormed projected

/-- A quoted value becomes a typed expression in any context. The complete
definition table supplies the types of constructor payloads. -/
theorem quoted_hasType {definitions : DataEnvironment} {world : StoreTyping} {value : Value} {code : Expr} {type : Ty}
    (quoted : Quoted value code) (typed : RuntimeValueHasType world value type definitions)
    (wellFormed : type.WellFormed definitions) (definitionsTyped : definitions.WellFormed)
    (context : Core.Context) : HasType context code type definitions := by
  induction quoted generalizing type with
  | unit => cases typed; exact .unit
  | bool => cases typed; exact .bool
  | word => cases typed; exact .word
  | integer => cases typed; exact .integer
  | pair left right first second =>
    cases typed with
    | pair firstTyped secondTyped =>
      cases wellFormed with
      | product firstWF secondWF => exact .pair (first firstTyped firstWF) (second secondTyped secondWF)
  | inLeft _ quoted ih =>
    cases typed with
    | inLeft typed =>
      cases wellFormed with
      | sum leftWF rightWF => exact .inLeft rightWF (ih typed leftWF)
  | inRight _ quoted ih =>
    cases typed with
    | inRight typed =>
      cases wellFormed with
      | sum leftWF rightWF => exact .inRight leftWF (ih typed rightWF)
  | constructed _ quoted ih =>
    cases typed with
    | constructed found typed =>
      exact .construct found (ih typed (definitionsTyped.constructorPayloadType_wellFormed found))

theorem Literal.native_hasType {fuel : Nat} {values : ValuesContext} {node : ExpressionNode}
    {sourceType : TypeSystem.Ty} {carrier : SourceCoreCompatibleValues.Value} {code : Expr} {type : Ty}
    (literal : Literal fuel values node sourceType carrier code)
    (projection : values.checked.catalog.project sourceType = .ok type)
    (wellFormed : type.WellFormed values.checked.catalog.definitions)
    (context : Core.Context) : HasType context code type values.checked.catalog.definitions := by
  cases literal with
  | encoded encoded _ _ quoted =>
    have same : encoded.type = type := Except.ok.inj (encoded.projected.symm.trans projection)
    exact quoted_hasType (quoted_of_quote quoted) (same ▸ encoded.typed []) wellFormed
      values.checked.definitionsTyped context

theorem ReadCode.native_hasType {fuel : Nat} {values : ValuesContext} {node : ExpressionNode}
    {declared : TypedBinder} {index : Nat} {type : Ty} {reason : Word} {code : Expr} {context : Core.Context}
    (emitted : ReadCode fuel values node declared index type reason code)
    (projection : values.checked.catalog.project declared.scheme.body = .ok type)
    (wellFormed : type.WellFormed values.checked.catalog.definitions)
    (reference : HasType context (.var index) (OptionalCell.referenceType type) values.checked.catalog.definitions) :
    HasType context code (LanguageResult.resultType type) values.checked.catalog.definitions := by
  cases emitted with
  | ordinary => exact OptionalCell.read_hasType reason wellFormed reference
  | mapping _ literal =>
    exact SourceCoreCompatibleDataExpressions.readMapping_hasType reference
      (literal.native_hasType projection wellFormed _)

/-- The static source declaration fixes the raw type of the lazily produced
empty mapping. Both branches use the actual compiler scope and checked type. -/
theorem Certificate.native_hasType {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel values source scope id reason code)
    {sourceContext : SourceSemantics.Context} (binding : StaticBinding certificate sourceContext)
    (wellFormed : certificate.type.WellFormed values.checked.catalog.definitions)
    (administrative : Core.Context) :
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code
      (LanguageResult.resultType certificate.type) values.checked.catalog.definitions := by
  have selected := SourceCoreLocalCell.lookup?_context certificate.slot
  have reference : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) (.var certificate.index)
      (OptionalCell.referenceType certificate.type) values.checked.catalog.definitions :=
    .var ((List.getElem?_append_left (List.getElem?_eq_some_iff.mp selected).1).trans selected)
  have projection : values.checked.catalog.project certificate.declared.scheme.body = .ok certificate.type := by
    rw [← values.checked.catalog.project_runtimeType certificate.declared.scheme.body,
      ← binding.occurrence, values.checked.catalog.project_runtimeType certificate.node.type]
    exact certificate.metadata.projected
  exact certificate.emitted.native_hasType projection wellFormed reference

/-- Actual accepted lowering and the independent source typing judgment close
native read typing. There is no child execution or native typing premise. -/
theorem loweredRead_native_hasType {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {sourceContext : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (accepted : SourceCoreCompatibleDataExpressions.lowerRead fuel values source scope id (reasonAt id) = .ok lowered.expression)
    (read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id = .ok (node, lowered.type))
    (unique : NodeOccurrencesUnique source) (declarations : ScopeDeclarations source scope sourceContext)
    (typed : ExpressionHasType source sourceContext id node.type) (administrative : Core.Context) :
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) values.checked.catalog.definitions := by
  obtain ⟨certificate, same, binding⟩ := loweredRead_of_accepted accepted read unique declarations typed
  have wellFormed := readExpression_wellFormed read
  rw [← same] at wellFormed
  simpa only [same] using certificate.native_hasType binding wellFormed administrative

/-- Generated frame and helper definitions can be appended without changing
the accepted read's code, local reference positions or native result type. -/
theorem loweredRead_native_hasType_at {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {sourceContext : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (accepted : SourceCoreCompatibleDataExpressions.lowerRead fuel values source scope id (reasonAt id) = .ok lowered.expression)
    (read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id = .ok (node, lowered.type))
    (unique : NodeOccurrencesUnique source) (declarations : ScopeDeclarations source scope sourceContext)
    (typed : ExpressionHasType source sourceContext id node.type) (administrative : Core.Context)
    {definitions : DataEnvironment} (extension : values.checked.catalog.definitions.Extends definitions) :
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) definitions :=
  (loweredRead_native_hasType accepted read unique declarations typed administrative).extend_definitions extension

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedLiteralEvidence
/-! Original expression typing and the actual covering dictionary supply a
numeric leaf's evidence. The Source ledger may retain an assumption that the
compiler replaced with an authenticated implementation. No equality between
those complete ledgers is needed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedLiteralEvidence
open Frontend SourceInference CompatibleExpressionLiterals

theorem of_typed {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    {evidence : Dynamic.EvidenceEnvironment}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id type)
    (idsUnique : RequirementIdsUnique context)
    (covers : evidence.Covers context) : NumericEvidence context evidence node := by
  intro literal resolution form
  cases typed with
  | intro contains raw _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    rw [form] at raw
    cases raw with
    | integerLiteral valid =>
      have proves : RequirementProves context resolution.requirement resolution.predicate := by
        cases valid with
        | word _ _ proves | integer _ _ proves => exact proves
      obtain ⟨closed, produced⟩ := Dynamic.RequirementProves.produces_of_covers covers proves
      exact ⟨proves, produced.excludes_unavailable idsUnique⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedLiteralEvidence
end

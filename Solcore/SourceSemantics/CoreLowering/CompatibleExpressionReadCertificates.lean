import Solcore.Frontend.SourceCoreCompatibleDataExpressions
import Solcore.SourceSemantics.WellFormed

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

import Solcore.Test.SourceCoreSelectedGeneralizedLocalSource
import Solcore.SourceSemantics.StaticValidation
import Solcore.SourceSemantics.CoreLowering.NumericLiteralEvidenceReceipts

/-! Proof-producing observations for the original generalized-local fixture.
Every accepted fact is checked against its complete source and lexical context;
native execution is not an input to these declarative typing proofs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation
open Solcore Core Frontend SourceInference SourceSemantics

def observe (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if proof : p then pure ⟨proof⟩ else throw (IO.userError message)

def admissible (context : SourceSemantics.Context) (type : TypeSystem.Ty) :
    IO (PLift (TypeAdmissible context type)) := do
  match accepted : validateTypeAdmissible context type with
  | .error _ => throw (IO.userError "generalized source type formation")
  | .ok () => return ⟨validateTypeAdmissible_success accepted⟩

def scheme (context : SourceSemantics.Context) (value : TypeSystem.Scheme) :
    IO (PLift (SchemeWellFormed context value)) := do
  match accepted : validateSchemeWellFormed context value with
  | .error _ => throw (IO.userError "generalized source scheme formation")
  | .ok () => return ⟨validateSchemeWellFormed_success accepted⟩

def generalizes (context : SourceSemantics.Context) (binder : TypedBinder) :
    IO (PLift (SchemeGeneralizesExcept context (localSchemeTemplateIds binder) binder.scheme)) := do
  match accepted : validateSchemeGeneralizesExcept context (localSchemeTemplateIds binder) binder.scheme with
  | .error _ => throw (IO.userError "generalized source exact generalization")
  | .ok () => return ⟨validateSchemeGeneralizesExcept_success accepted⟩

def binder (context : SourceSemantics.Context) (owner : Resolved.DeclarationId) (value : TypedBinder) :
    IO (PLift (BinderExtends owner context value
      (context.withLocal value.id value.scheme value.schemeRequirements))) := do
  let ⟨owned⟩ ← observe (value.id.owner = owner) "generalized source binder owner"
  let ⟨formed⟩ ← scheme context value.scheme
  let ⟨fresh⟩ ← observe (value.id ∉ context.locals.map Prod.fst ∧
    value.id ∉ context.localSchemeRequirements.map Prod.fst) "generalized source binder freshness"
  let ⟨quantifiers⟩ ← observe (value.scheme.quantified.all (fun metavariable =>
    decide (metavariable ∉ context.typeVariables) && context.locals.all (fun entry =>
      decide (metavariable ∉ entry.2.quantified))) = true) "generalized source quantifier freshness"
  let ⟨empty⟩ ← observe (value.scheme.quantified = [] → value.schemeRequirements = [])
    "generalized source monomorphic requirements"
  have isolated : SchemeQuantifiersFresh context value.scheme := by
    intro metavariable member
    have selected := List.all_eq_true.mp quantifiers metavariable member
    simp only [Bool.and_eq_true] at selected
    exact ⟨of_decide_eq_true selected.1, fun entry found =>
      of_decide_eq_true (List.all_eq_true.mp selected.2 entry found)⟩
  return ⟨.intro ⟨owned, formed, isolated, empty⟩ fresh⟩

def range (context : SourceSemantics.Context) : (substitution : TypeSystem.Substitution) →
    IO (PLift (SubstitutionRangeAdmissible context substitution))
  | [] => pure ⟨by intro metavariable replacement member; cases member⟩
  | (metavariable, replacement) :: rest => do
    let ⟨head⟩ ← admissible context replacement
    let ⟨tail⟩ ← range context rest
    return ⟨by
      intro other value member
      obtain same | member := List.mem_cons.mp member
      · cases same; exact head
      · exact tail other value member⟩

def read {source : TypedSource} {value : TypedBinder} {type : TypeSystem.Ty}
    (node : Tests.SourceCoreNamedBranch.Read source value type) (context : SourceSemantics.Context)
    (lookup : context.LocalLookup value.id value.scheme)
    (requirements : context.LocalSchemeRequirementsLookup value.id value.schemeRequirements) :
    IO (PLift (ExpressionHasType source context node.node.id type)) := do
  let ⟨empty⟩ ← observe (value.schemeRequirements = []) "generalized unqualified read"
  let ⟨formed⟩ ← scheme context value.scheme
  let ⟨typeFormed⟩ ← admissible context type
  let some matched := value.scheme.matchInstanceCertificate? type
    | throw (IO.userError "generalized exact local instance")
  let ⟨replacements⟩ ← range context matched.substitution
  have instanceValid : LocalSchemeInstantiationValid context value type [] :=
    .intro (LocalSchemeRequirementsWellFormed.empty _ _ empty) formed matched.substitution
      ⟨matched.quantifiedUnique, matched.domainExact ▸ List.Perm.refl _⟩ replacements matched.applies
      (by simp) (by intro id member; cases member)
      (by rw [instantiateLocalSchemePredicates, empty]; exact .nil)
  have typed : ExpressionHasType source context node.node.id node.node.type := by
    refine .intro (lookupExpression?_sound node.found)
      (node.form ▸ ExpressionFormHasRawType.reference (.local lookup requirements instanceValid))
      node.raw typeFormed (node.type.symm ▸ typeFormed) ?_
    rw [node.requirements, node.coercions, node.type]
    exact .ordinary (by intro id member; cases member) (.nil _) rfl
  return ⟨Eq.mp (congrArg (fun target => ExpressionHasType source context node.node.id target) node.type) typed⟩

def uncoerced {source : TypedSource} (context : SourceSemantics.Context)
    (node : ExpressionNode) (type : TypeSystem.Ty)
    (found : source.lookupExpression? node.id = some node)
    (form : ExpressionFormHasRawType source context node.form type (.ordinary [])) :
    IO (PLift (ExpressionHasType source context node.id type)) := do
  let ⟨raw⟩ ← observe (node.rawType = type) "generalized source raw type"
  let ⟨result⟩ ← observe (node.type = type) "generalized source result type"
  let ⟨requirements⟩ ← observe (node.requirements = []) "generalized source empty requirements"
  let ⟨coercions⟩ ← observe (node.coercions = []) "generalized source empty coercions"
  let ⟨formed⟩ ← admissible context type
  have typed : ExpressionHasType source context node.id node.type := by
    refine .intro (lookupExpression?_sound found) form raw formed (result.symm ▸ formed) ?_
    rw [requirements, coercions, result]
    exact .ordinary (by intro id member; cases member) (.nil _) rfl
  return ⟨by simpa only [result] using typed⟩

def call {source : TypedSource} {binder : TypedBinder} {argument : ExpressionId} {type : TypeSystem.Ty}
    (shape : CallShape source binder argument type) (context : SourceSemantics.Context)
    (callee : ExpressionHasType source context shape.callee.node.id (.function type type))
    (argumentTyped : ExpressionHasType source context argument type) :
    IO (PLift (ExpressionHasType source context shape.node.id type)) := do
  let ⟨before⟩ ← observe (shape.metadata.argumentTypeBeforeCoercion = type) "generalized call argument before"
  let ⟨after⟩ ← observe (shape.metadata.argumentTypeAfterCoercion = type) "generalized call argument after"
  let ⟨raw⟩ ← observe (shape.node.rawType = type) "generalized call raw type"
  let ⟨result⟩ ← observe (shape.node.type = type) "generalized call result type"
  let ⟨formed⟩ ← admissible context type
  have application : IndirectApplicationValid context shape.metadata [type] type := by
    refine .intro shape.arity before after ?_
    rw [before, shape.argumentCoercions]
    exact .nil _
  have typed : ExpressionHasType source context shape.node.id shape.node.type := by
    refine .intro (lookupExpression?_sound shape.found)
      (shape.form ▸ ExpressionFormHasRawType.indirectCall callee (.cons argumentTyped (.nil _)) application)
      raw formed (result.symm ▸ formed) ?_
    rw [shape.requirements, shape.coercions, shape.argumentCoercions, result]
    exact .indirectCall (by intro step member; cases member) (.nil _) rfl
  return ⟨by simpa only [result] using typed⟩

private theorem builtin_word (context : SourceSemantics.Context) :
    RetainedEvidenceValid context.assumptions context.signatures.resolutionRules
      (ProgramSignatures.builtinIntPredicate .word)
      (.implementation (.byImpl (ProgramSignatures.builtinIntPredicate .word) (.builtin .intWord) [])) := by
  apply RetainedEvidenceValid.intro (.implementation (.byImpl .nil))
  exact .implementation (rule := ProgramSignatures.builtinIntWordRule)
    (by simp [ProgramSignatures.resolutionRules, ProgramSignatures.builtinResolutionRules]) rfl
    (.intro ⟨[], []⟩ ⟨ParameterSubstitution.exact_empty, ExactSubstitution.empty⟩ rfl rfl) .nil

def word {source : TypedSource} (shape : WordNode source) (context : SourceSemantics.Context) :
    IO (PLift (ExpressionHasType source context shape.node.id .word)) := do
  match accepted : SourceCoreElaboration.validateWordIntegerLiteral context.solvedRequirements
      shape.node shape.literal shape.resolution with
  | .error _ => throw (IO.userError "generalized original Word evidence")
  | .ok validated =>
    let ⟨formed⟩ ← admissible context .word
    let ⟨raw⟩ ← observe (shape.node.rawType = .word) "generalized original Word raw type"
    have metadata := SourceCoreElaboration.validateWordIntegerLiteral_sound accepted
    have proves : RequirementProves context shape.resolution.requirement
        (ProgramSignatures.builtinIntPredicate shape.resolution.targetType) := by
      obtain ⟨row, selected, predicate, evidence⟩ := CoreLowering.NumericLiteralEvidenceReceipts.word accepted
      have member : row ∈ context.solvedRequirements.filter (fun row => decide (row.id = shape.resolution.requirement)) := by
        rw [selected]; simp
      obtain ⟨member, identity⟩ := List.mem_filter.mp member
      refine ⟨row, ⟨member, of_decide_eq_true identity⟩, predicate, .intro ?_⟩
      rw [evidence, predicate]
      simpa only [IntegerLiteralResolution.predicate, metadata.targetType] using builtin_word context
    have valid : IntegerLiteralValid context shape.literal shape.resolution :=
      .word metadata.meaning metadata.targetType proves
    have typed : ExpressionHasType source context shape.node.id shape.node.type := by
      refine .intro (lookupExpression?_sound shape.found)
        (shape.form ▸ ExpressionFormHasRawType.integerLiteral valid)
        (raw.trans metadata.targetType.symm) (metadata.targetType.symm ▸ formed)
        (metadata.nodeType.symm ▸ formed) ?_
      rw [metadata.requirements, metadata.coercions, metadata.targetType, metadata.nodeType]
      exact .ordinary (by intro id member; exact List.mem_singleton.mp member ▸ valid.requirement_valid) (.nil _) rfl
    return ⟨by simpa only [metadata.nodeType] using typed⟩

end Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation

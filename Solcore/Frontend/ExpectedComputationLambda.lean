import Solcore.Frontend.ExpectedUnaryLambdaHeader
import Solcore.Frontend.ComputationReturnTreeProperties
import Solcore.Frontend.ComputationReturnTreeTypingProperties

/-!
Standalone expected-type lambda elaboration retains the original header and body.
It does not extend existing source entry points, construct runtime captures, or
claim canonical backend execution or source-to-Core operational correspondence.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- The original header, representable component types and original body evidence
jointly determine a literal Core lambda, independently of any executable checker. -/
inductive ExpectedComputationLambdaElaborates
    (ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (initial : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | lambda {source : Syntax.Expr} {expected : Core.Ty}
      {header : DeclaredUnaryLambdaHeader} {bodyCore : Core.Expr}
      (headerDeclaration : ExpectedUnaryLambdaHeaderDeclares types owner initial source expected header)
      (parameterWellFormed : Core.Ty.WellFormed [] header.parameterType)
      (returnWellFormed : Core.Ty.WellFormed [] header.returnType)
      (bodyElaboration : ComputationReturnTreeElaborates ChildElab types owner
        header.inputs header.body bodyCore header.returnType) :
      ExpectedComputationLambdaElaborates ChildElab types owner initial source
        (.lambda header.parameterType header.returnType bodyCore) expected

/-- Check the original expected header and component types, then require the
unchanged shared body checker to return exactly the expected codomain. -/
def elaborateExpectedComputationLambda?
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (initial : LocalTypeInputs)
    (source : Syntax.Expr) (expected : Core.Ty) : Option Core.Expr := do
  let header ← declareExpectedUnaryLambdaHeader? types owner initial source expected
  if header.parameterType.isWellFormed [] && header.returnType.isWellFormed [] then
    let (bodyCore, bodyType) ← elaborateComputationReturnTree? checkChild types owner header.inputs header.body
    if bodyType = header.returnType then
      some (.lambda header.parameterType header.returnType bodyCore)
    else none
  else none

variable {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}

/-- Exact checking uses only the fixed child's own checker correspondence. -/
theorem elaborateExpectedComputationLambda?_iff
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Expr} {expected : Core.Ty} {core : Core.Expr} :
    elaborateExpectedComputationLambda? checkChild types owner initial source expected = some core ↔
      ExpectedComputationLambdaElaborates ChildElab types owner initial source core expected := by
  constructor
  · intro accepted
    cases headerChecked : declareExpectedUnaryLambdaHeader? types owner initial source expected with
    | none => simp only [elaborateExpectedComputationLambda?, headerChecked, bind, Option.bind_none, reduceCtorEq] at accepted
    | some header =>
        simp only [elaborateExpectedComputationLambda?, headerChecked, bind, Option.bind_some] at accepted
        split at accepted
        · rename_i wellFormed
          simp only [Bool.and_eq_true] at wellFormed
          obtain ⟨parameterWellFormed, returnWellFormed⟩ := wellFormed
          cases bodyChecked : elaborateComputationReturnTree? checkChild types owner header.inputs header.body with
          | none => simp only [bodyChecked, Option.bind_none, reduceCtorEq] at accepted
          | some result =>
              rcases result with ⟨bodyCore, bodyType⟩
              simp only [bodyChecked, Option.bind_some] at accepted
              split at accepted
              · rename_i same
                subst bodyType
                cases Option.some.inj accepted
                exact .lambda (declareExpectedUnaryLambdaHeader?_iff.mp headerChecked)
                  (Core.Ty.isWellFormed_sound parameterWellFormed)
                  (Core.Ty.isWellFormed_sound returnWellFormed)
                  ((elaborateComputationReturnTree?_iff childCorrect).mp bodyChecked)
              · cases accepted
        · cases accepted
  · intro elaboration
    cases elaboration with
    | lambda header parameterWellFormed returnWellFormed body =>
        simp only [elaborateExpectedComputationLambda?, declareExpectedUnaryLambdaHeader?_iff.mpr header,
          bind, Option.bind_some, Core.Ty.isWellFormed_complete parameterWellFormed,
          Core.Ty.isWellFormed_complete returnWellFormed, Bool.true_and, ite_true,
          (elaborateComputationReturnTree?_iff childCorrect).mpr body]

/-- Rejection is exact absence in this opt-in fixed Core profile. -/
theorem elaborateExpectedComputationLambda?_eq_none_iff
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Expr} {expected : Core.Ty} :
    elaborateExpectedComputationLambda? checkChild types owner initial source expected = none ↔
      ¬ ∃ core, ExpectedComputationLambdaElaborates ChildElab types owner initial source core expected := by
  constructor
  · intro rejected ⟨core, elaboration⟩
    have accepted := (elaborateExpectedComputationLambda?_iff childCorrect).mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateExpectedComputationLambda? checkChild types owner initial source expected with
    | none => rfl
    | some core => exact False.elim (absent ⟨core, (elaborateExpectedComputationLambda?_iff childCorrect).mp accepted⟩)

/-- Core typing uses only child Core typing, not child checker correctness.
No blanket well-formedness assumption is imposed on the outer local context. -/
theorem ExpectedComputationLambdaElaborates.core_hasType
    (childCoreType : ∀ {table context source core type},
      ChildElab table context source core type → Core.HasType context.values core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {expected : Core.Ty}
    (elaboration : ExpectedComputationLambdaElaborates ChildElab types owner initial source core expected) :
    Core.HasType initial.context.values core expected := by
  cases elaboration with
  | lambda header parameterWellFormed returnWellFormed body =>
      obtain ⟨_, _, _, _, _, _, _, expectedShape, _, _, inputsEq, _⟩ := header.provenance_and_layout
      rw [expectedShape]
      apply Core.HasType.lambda parameterWellFormed returnWellFormed
      have bodyType := body.core_hasType childCoreType
      rw [inputsEq] at bodyType
      simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.values,
        List.map_cons, Prod.snd] using bodyType

/-- Preserve original header/body evidence and exact lambda shape. The retained
header evidence supplies all original spans and the fresh-row scope layout. -/
theorem ExpectedComputationLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {expected : Core.Ty}
    (elaboration : ExpectedComputationLambdaElaborates ChildElab types owner initial source core expected) :
    ∃ header bodyCore,
      ExpectedUnaryLambdaHeaderDeclares types owner initial source expected header ∧
      Core.Ty.WellFormed [] header.parameterType ∧ Core.Ty.WellFormed [] header.returnType ∧
      ComputationReturnTreeElaborates ChildElab types owner header.inputs header.body bodyCore header.returnType ∧
      core = .lambda header.parameterType header.returnType bodyCore := by
  cases elaboration with
  | lambda header parameterWellFormed returnWellFormed body =>
      exact ⟨_, _, header, parameterWellFormed, returnWellFormed, body, rfl⟩

end Solcore.Frontend

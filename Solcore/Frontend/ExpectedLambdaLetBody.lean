import Solcore.Frontend.ExpectedComputationLambda

/-!
One original leading typed let passes its annotation to a lambda initializer.
The initializer uses the original outer scope; only the untouched shared tail
receives the new binding. Existing source entry points and raw evaluation are unchanged.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Original annotation, expected initializer and post-binding tail evidence determine a literal Core let. -/
inductive ExpectedLambdaLetBodyElaborates
    (ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (initial : LocalTypeInputs) :
    Syntax.Block → Core.Expr → Core.Ty → Prop where
  | binding {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {declaredType returnType : Core.Ty} {initializerCore tailCore : Core.Expr}
      (meaning : StructuralTypeDenotes types annotation declaredType)
      (initializerElaboration : ExpectedComputationLambdaElaborates ChildElab types owner
        initial initializer initializerCore declaredType)
      (tailElaboration : ComputationReturnTreeElaborates ChildElab types owner
        (initial.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ tailCore returnType) :
      ExpectedLambdaLetBodyElaborates ChildElab types owner initial
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩
        (.letE initializerCore tailCore) returnType

/-- Check only an explicitly typed lambda-let head, then reuse the unchanged shared tail checker. -/
def elaborateExpectedLambdaLetBody?
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (initial : LocalTypeInputs)
    (source : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  match source with
  | ⟨blockSpan, ⟨_, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ => do
      let declaredType ← interpretStructuralType? types annotation
      let initializerCore ← elaborateExpectedComputationLambda? checkChild types owner initial initializer declaredType
      let (tailCore, returnType) ← elaborateComputationReturnTree? checkChild types owner
        (initial.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩
      return (.letE initializerCore tailCore, returnType)
  | _ => none

variable {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}

/-- Exact checking requires only the fixed child's checker/elaboration correspondence. -/
theorem elaborateExpectedLambdaLetBody?_iff
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateExpectedLambdaLetBody? checkChild types owner initial source = some (core, type) ↔
      ExpectedLambdaLetBodyElaborates ChildElab types owner initial source core type := by
  constructor
  · intro accepted
    unfold elaborateExpectedLambdaLetBody? at accepted
    split at accepted
    · rename_i blockSpan letSpan name annotation initializer rest
      simp only [bind, Option.bind_eq_some_iff] at accepted
      obtain ⟨declaredType, meaning, initializerCore, initializerAccepted, tailResult, tailAccepted, resultEq⟩ := accepted
      rcases tailResult with ⟨tailCore, returnType⟩
      cases Option.some.inj resultEq
      exact .binding (interpretStructuralType?_iff.mp meaning)
        ((elaborateExpectedComputationLambda?_iff childCorrect).mp initializerAccepted)
        ((elaborateComputationReturnTree?_iff childCorrect).mp tailAccepted)
    · cases accepted
  · intro elaboration
    cases elaboration with
    | binding meaning initializer tail =>
        simp only [elaborateExpectedLambdaLetBody?, (interpretStructuralType?_iff).mpr meaning,
          bind, Option.bind_some, pure, (elaborateExpectedComputationLambda?_iff childCorrect).mpr initializer,
          (elaborateComputationReturnTree?_iff childCorrect).mpr tail]

/-- Rejection is absence in this opt-in profile, not a language-wide invalidity judgment. -/
theorem elaborateExpectedLambdaLetBody?_eq_none_iff
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} :
    elaborateExpectedLambdaLetBody? checkChild types owner initial source = none ↔
      ¬ ∃ core type, ExpectedLambdaLetBodyElaborates ChildElab types owner initial source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted := (elaborateExpectedLambdaLetBody?_iff childCorrect).mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateExpectedLambdaLetBody? checkChild types owner initial source with
    | none => rfl
    | some result => exact False.elim (absent ⟨_, _, (elaborateExpectedLambdaLetBody?_iff childCorrect).mp accepted⟩)

/-- Core typing uses only child Core typing, independently of checking or runtime assumptions. -/
theorem ExpectedLambdaLetBodyElaborates.core_hasType
    (childCoreType : ∀ {table context source core type},
      ChildElab table context source core type → Core.HasType context.values core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ExpectedLambdaLetBodyElaborates ChildElab types owner initial source core type) :
    Core.HasType initial.context.values core type := by
  cases elaboration with
  | binding meaning initializer tail =>
      exact .letE (initializer.core_hasType childCoreType)
        (by simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.values,
          List.map_cons, Prod.snd] using tail.core_hasType childCoreType)

/-- Preserve the exact original head/tail, pre-binder initializer scope and fresh tail-row layout. -/
theorem ExpectedLambdaLetBodyElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ExpectedLambdaLetBodyElaborates ChildElab types owner initial source core type) :
    ∃ blockSpan letSpan name annotation initializer rest declaredType initializerCore tailCore,
      source = ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ ∧
      StructuralTypeDenotes types annotation declaredType ∧
      ExpectedComputationLambdaElaborates ChildElab types owner initial initializer initializerCore declaredType ∧
      ComputationReturnTreeElaborates ChildElab types owner
        (initial.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ tailCore type ∧
      core = .letE initializerCore tailCore ∧
      (initial.bindFresh owner name.value declaredType).bindings =
        { name := name.value, id := Resolved.freshLocalId owner initial.ids, type := declaredType } :: initial.bindings := by
  cases elaboration with
  | binding meaning initializer tail =>
      exact ⟨_, _, _, _, _, _, _, _, _, rfl, meaning, initializer, tail, rfl,
        LocalTypeInputs.bindFresh_bindings _ _ _ _⟩

end Solcore.Frontend

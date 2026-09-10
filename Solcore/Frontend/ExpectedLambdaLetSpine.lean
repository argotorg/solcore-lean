import Solcore.Frontend.ExpectedComputationLambda

/-!
A pure original-source boundary selects consecutive explicitly typed lambda lets.
Recognized heads use the current pre-binder scope and never fall back on failure.
At the first non-head, the entire remaining body uses the unchanged shared checker.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Inspect only the original typed-let/direct-lambda shape, not any type or header validity. -/
def isExpectedLambdaLetHead : Syntax.Block → Bool
  | ⟨_, ⟨_, .letDecl _ (some _) (some ⟨_, .lambda _ _ _ _⟩)⟩ :: _⟩ => true
  | _ => false

/-- Disjoint original terminal/head derivations preserve each initializer and fresh tail scope. -/
inductive ExpectedLambdaLetSpineElaborates
    (ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    LocalTypeInputs → Syntax.Block → Core.Expr → Core.Ty → Prop where
  | terminal {initial : LocalTypeInputs} {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
      (boundary : isExpectedLambdaLetHead source = false)
      (body : ComputationReturnTreeElaborates ChildElab types owner initial source core type) :
      ExpectedLambdaLetSpineElaborates ChildElab types owner initial source core type
  | binding {initial : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {declaredType returnType : Core.Ty} {initializerCore tailCore : Core.Expr}
      (head : isExpectedLambdaLetHead
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ = true)
      (meaning : StructuralTypeDenotes types annotation declaredType)
      (initializerElaboration : ExpectedComputationLambdaElaborates ChildElab types owner
        initial initializer initializerCore declaredType)
      (tailElaboration : ExpectedLambdaLetSpineElaborates ChildElab types owner
        (initial.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ tailCore returnType) :
      ExpectedLambdaLetSpineElaborates ChildElab types owner initial
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩
        (.letE initializerCore tailCore) returnType

/-- Check the maximal direct-lambda prefix; true-boundary failure never delegates to the old body. -/
def elaborateExpectedLambdaLetSpine?
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (initial : LocalTypeInputs)
    (source : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  if isExpectedLambdaLetHead source = false then
    elaborateComputationReturnTree? checkChild types owner initial source
  else match source with
  | ⟨blockSpan, ⟨_, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ => do
      let declaredType ← interpretStructuralType? types annotation
      let initializerCore ← elaborateExpectedComputationLambda? checkChild types owner initial initializer declaredType
      let (tailCore, returnType) ← elaborateExpectedLambdaLetSpine? checkChild types owner
        (initial.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩
      return (.letE initializerCore tailCore, returnType)
  | _ => none
termination_by sizeOf source
decreasing_by simp_wf; omega

variable {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}

private theorem checker_sound
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateExpectedLambdaLetSpine? checkChild types owner initial source = some (core, type)) :
    ExpectedLambdaLetSpineElaborates ChildElab types owner initial source core type := by
  unfold elaborateExpectedLambdaLetSpine? at accepted
  split at accepted
  · rename_i boundary
    exact .terminal boundary ((elaborateComputationReturnTree?_iff childCorrect).mp accepted)
  · rename_i notTerminal
    have head : isExpectedLambdaLetHead source = true := by
      cases equality : isExpectedLambdaLetHead source <;> simp_all
    split at accepted
    · rename_i blockSpan letSpan name annotation initializer rest
      simp only [bind, Option.bind_eq_some_iff] at accepted
      obtain ⟨declaredType, meaning, initializerCore, initializerAccepted, tailResult, tailAccepted, resultEq⟩ := accepted
      rcases tailResult with ⟨tailCore, returnType⟩
      cases Option.some.inj resultEq
      exact .binding head (interpretStructuralType?_iff.mp meaning)
        ((elaborateExpectedComputationLambda?_iff childCorrect).mp initializerAccepted)
        (checker_sound childCorrect tailAccepted)
    · cases accepted
termination_by sizeOf source
decreasing_by subst source; simp_wf; omega

/-- Exact correspondence needs only the fixed child's checker/elaboration law. -/
theorem elaborateExpectedLambdaLetSpine?_iff
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateExpectedLambdaLetSpine? checkChild types owner initial source = some (core, type) ↔
      ExpectedLambdaLetSpineElaborates ChildElab types owner initial source core type := by
  constructor
  · exact checker_sound childCorrect
  · intro elaboration
    induction elaboration with
    | terminal boundary body =>
        unfold elaborateExpectedLambdaLetSpine?
        simpa only [boundary, ite_true] using (elaborateComputationReturnTree?_iff childCorrect).mpr body
    | binding head meaning initializer tail ih =>
        unfold elaborateExpectedLambdaLetSpine?
        simp only [head, reduceCtorEq, ite_false, (interpretStructuralType?_iff).mpr meaning,
          bind, Option.bind_some, pure, (elaborateExpectedComputationLambda?_iff childCorrect).mpr initializer, ih]

/-- Rejection is exact absence in this opt-in profile, including unsupported true-boundary heads. -/
theorem elaborateExpectedLambdaLetSpine?_eq_none_iff
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} :
    elaborateExpectedLambdaLetSpine? checkChild types owner initial source = none ↔
      ¬ ∃ core type, ExpectedLambdaLetSpineElaborates ChildElab types owner initial source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted := (elaborateExpectedLambdaLetSpine?_iff childCorrect).mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateExpectedLambdaLetSpine? checkChild types owner initial source with
    | none => rfl
    | some result => exact False.elim (absent ⟨_, _, (elaborateExpectedLambdaLetSpine?_iff childCorrect).mp accepted⟩)

/-- Core typing requires only child Core typing, not checking or runtime assumptions. -/
theorem ExpectedLambdaLetSpineElaborates.core_hasType
    (childCoreType : ∀ {table context source core type},
      ChildElab table context source core type → Core.HasType context.values core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ExpectedLambdaLetSpineElaborates ChildElab types owner initial source core type) :
    Core.HasType initial.context.values core type := by
  induction elaboration with
  | terminal boundary body => exact body.core_hasType childCoreType
  | binding head meaning initializer tail ih =>
      exact .letE (initializer.core_hasType childCoreType)
        (by simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.values, List.map_cons, Prod.snd] using ih)

/-- One-layer inversion retains either the old terminal or the exact original head and fresh tail row. -/
theorem ExpectedLambdaLetSpineElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ExpectedLambdaLetSpineElaborates ChildElab types owner initial source core type) :
    (isExpectedLambdaLetHead source = false ∧
      ComputationReturnTreeElaborates ChildElab types owner initial source core type) ∨
    ∃ blockSpan letSpan name annotation initializer rest declaredType initializerCore tailCore,
      isExpectedLambdaLetHead source = true ∧
      source = ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ ∧
      StructuralTypeDenotes types annotation declaredType ∧
      ExpectedComputationLambdaElaborates ChildElab types owner initial initializer initializerCore declaredType ∧
      ExpectedLambdaLetSpineElaborates ChildElab types owner
        (initial.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ tailCore type ∧
      core = .letE initializerCore tailCore ∧
      (initial.bindFresh owner name.value declaredType).bindings =
        { name := name.value, id := Resolved.freshLocalId owner initial.ids, type := declaredType } :: initial.bindings := by
  cases elaboration with
  | terminal boundary body => exact .inl ⟨boundary, body⟩
  | binding head meaning initializer tail =>
      exact .inr ⟨_, _, _, _, _, _, _, _, _, head, rfl, meaning, initializer, tail, rfl,
        LocalTypeInputs.bindFresh_bindings _ _ _ _⟩

end Solcore.Frontend

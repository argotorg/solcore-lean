import Solcore.SourceSemantics.CoreLowering.DataHeap
import Solcore.SourceSemantics.CoreLowering.DataPatternDecision

/-! Authenticated binder payloads from a static pattern certificate. The source
binder's declared type is retained separately from its Core projection. These
facts permit ordinary heap allocation after a successful match without treating
an untyped value relation or a matching Core tag as source type evidence. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPatternBindings
open Core Frontend Frontend.SourceInference
open SourceCoreDataMatches DataPatternCertificates DataPatternValues DataPatternLeaves
open DataPatternTypedValues DataPatternSuccess DataPatternExecution

inductive BindingsRep (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures) :
    List (TypedBinder × Ty) → List (TypedBinder × Dynamic.Value) → List Value → Prop where
  | nil : BindingsRep catalog signatures [] [] []
  | cons {binder : TypedBinder} {type : Ty} {source : Dynamic.Value} {value : Value}
      {binders : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
      (projection : catalog.project binder.scheme.body = .ok type)
      (head : TypedValueRep catalog signatures binder.scheme.body source value)
      (tail : BindingsRep catalog signatures binders sources values) :
      BindingsRep catalog signatures ((binder, type) :: binders) ((binder, source) :: sources) (value :: values)

theorem BindingsRep.erase {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {binders : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
    (represented : BindingsRep catalog signatures binders sources values) :
    DataPatternLeaves.BindingsRep catalog binders sources values := by
  induction represented with
  | nil => exact .nil
  | cons _ head _ ih => exact .cons head.erase ih

theorem BindingsRep.append {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {a c : List (TypedBinder × Ty)} {b d : List (TypedBinder × Dynamic.Value)} {v w : List Value}
    (left : BindingsRep catalog signatures a b v) (right : BindingsRep catalog signatures c d w) :
    BindingsRep catalog signatures (a ++ c) (b ++ d) (v ++ w) := by
  induction left with
  | nil => exact right
  | cons projection head _ ih => exact .cons projection head ih

/-- The checked projection retains the same raw catalog type. -/
theorem projected_raw {compilation : Compilation} {source : TypedSource} {type : TypeSystem.Ty} {coreType : Ty}
    (accepted : projected compilation source type = .ok coreType) :
    compilation.checked.catalog.project type = .ok coreType := by
  unfold projected SourceCoreGeneralTypes.projectType at accepted
  cases checked : compilation.checked.project type with
  | error error => simp [checked, Except.mapError, Except.map] at accepted
  | ok projection =>
    simp only [checked, Except.map, Except.mapError, Except.ok.injEq] at accepted
    subst coreType
    unfold SourceCoreDataCatalog.Checked.project at checked
    cases raw : compilation.checked.catalog.project type with
    | error error => simp [raw, bind, Except.bind] at checked
    | ok actual =>
      simp only [raw, bind, Except.bind] at checked
      split at checked
      · cases checked; rfl
      · cases checked

def TreeBindingTypes (compilation : Compilation) (context : SourceSemantics.Context)
    (type : TypeSystem.Ty) (instructions : List MatchPatternInstruction) (pattern : Pattern)
    (rest : List MatchPatternInstruction) : Prop :=
  ∀ source value bindings sourceRest,
    TypedValueRep compilation.checked.catalog compilation.signatures type source value →
    Dynamic.PatternInstructionMatches context source instructions bindings sourceRest →
    ∃ values, sourceRest = rest ∧ BindingsRep compilation.checked.catalog compilation.signatures pattern.bindings bindings values

def ForestBindingTypes (compilation : Compilation) (context : SourceSemantics.Context)
    (types : List TypeSystem.Ty) (instructions : List MatchPatternInstruction) (patterns : List Pattern)
    (rest : List MatchPatternInstruction) : Prop :=
  ∀ sources values bindings sourceRest,
    TypedValuesRep compilation.checked.catalog compilation.signatures types sources values →
    Dynamic.PatternInstructionsMatch context sources instructions bindings sourceRest →
    ∃ boundValues, sourceRest = rest ∧
      BindingsRep compilation.checked.catalog compilation.signatures (patterns.flatMap (·.bindings)) bindings boundValues

/-- Pattern structure, genuine source matching, and the authenticated input
value determine the source types of every allocated binder. No evaluator
premise or heap invariant is needed to derive this certificate. -/
theorem Tree.binding_types {compilation : Compilation} {context : SourceSemantics.Context} {source : TypedSource}
    {site : StatementId} {span : Syntax.SourceSpan} {scope : Scope} {type : TypeSystem.Ty}
    {instructions rest : List MatchPatternInstruction} {pattern : Pattern}
    (tree : Tree compilation source site span scope type instructions pattern rest) :
    TreeBindingTypes compilation context type instructions pattern rest := by
  induction tree using Tree.rec
      (motive_2 := fun types instructions patterns rest _ => ForestBindingTypes compilation context types instructions patterns rest) with
  | wildcard projection =>
    intro source value bindings sourceRest represented matched
    cases matched
    exact ⟨[], rfl, .nil⟩
  | binder projection sourceType valid =>
    intro source value bindings sourceRest represented matched
    cases matched
    refine ⟨[value], rfl, .cons ?_ ?_ .nil⟩
    · rw [sourceType]; exact projected_raw projection
    · rw [sourceType]; exact represented
  | literal projection validated =>
    intro source value bindings sourceRest represented matched
    cases matched
    exact ⟨[], rfl, .nil⟩
  | @tuple expected coreType count types instructions rest children coreTypes projection unpacked childrenTree projectedChildren ih =>
    intro sourceValue value bindings sourceRest represented matched
    cases matched with
    | tuple packed arity matchedChildren =>
      obtain ⟨sources, values, representations, packing, valueEq⟩ := TypedValueRep.unpack unpacked represented
      have sameSources := Dynamic.ValuesPack.injective_of_length_eq packing packed
        ((TypedValuesRep.length representations).1.symm.trans ((unpackTypes_length unpacked).trans arity.symm))
      subst sources
      exact ih _ _ _ _ representations matchedChildren
  | constructor projection result arity resolved sameType childrenTree projectedChildren registered ih =>
    intro sourceValue value bindings sourceRest represented matched
    cases matched with
    | constructor agreement countEq matchedChildren =>
      cases represented with
      | constructed nominal actualResult authenticated payloads =>
        exact ih _ _ _ _ (agreement.payload_types_eq ▸ payloads) matchedChildren
  | nil =>
    intro sources values bindings sourceRest represented matched
    cases represented
    cases matched
    exact ⟨[], rfl, .nil⟩
  | cons headTree tailTree headIH tailIH =>
    intro sources values bindings sourceRest represented matched
    cases represented with
    | cons valueRep valuesRep =>
      cases matched with
      | cons headMatch tailMatch =>
        obtain ⟨headValues, headRestEq, headBindings⟩ := headIH _ _ _ _ valueRep headMatch
        subst headRestEq
        obtain ⟨tailValues, tailRestEq, tailBindings⟩ := tailIH _ _ _ _ valuesRep tailMatch
        exact ⟨headValues ++ tailValues, tailRestEq, headBindings.append tailBindings⟩
/-- The source value and fixed catalog determine its finite Core carrier. -/
theorem value_core_unique {catalog : SourceCoreDataCatalog.Catalog}
    {source : Dynamic.Value} {left right : Value}
    (first : ValueRep catalog source left) (second : ValueRep catalog source right) : left = right := by
  induction first using ValueRep.rec
      (motive_2 := fun sources values _ => ∀ other, ValuesRep catalog sources other → values = other)
      generalizing right with
  | unit => cases second; rfl
  | bool => cases second; rfl
  | word => cases second; rfl
  | integer => cases second; rfl
  | product leftRep rightRep leftIH rightIH =>
    cases second with
    | product otherLeft otherRight => rw [leftIH otherLeft, rightIH otherRight]
  | constructed selected payloads ih =>
    cases second with
    | constructed otherSelected otherPayloads =>
      have same := Option.some.inj (selected.symm.trans otherSelected)
      cases same
      rw [ih _ otherPayloads]
  | nil => rename_i other represented; cases represented; rfl
  | cons head tail headIH tailIH =>
    rename_i other represented
    cases represented with
    | cons first rest => rw [headIH first, tailIH _ rest]

theorem bindings_core_unique {catalog : SourceCoreDataCatalog.Catalog}
    {binders : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {left right : List Value}
    (first : DataPatternLeaves.BindingsRep catalog binders sources left)
    (second : DataPatternLeaves.BindingsRep catalog binders sources right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons head tail ih =>
    cases second with
    | cons otherHead otherTail => rw [value_core_unique head otherHead, ih otherTail]

/-- The binder bundle already produced by the established matcher theorem has
these exact authenticated payloads, not merely some other typed bundle. -/
theorem Certificate.bindings_typed {compilation : Compilation} {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : Certificate compilation source scope site span expected pattern compiled)
    (signatures : context.signatures = compilation.signatures)
    {sourceValue : Dynamic.Value} {value : Value} {bindings : List (TypedBinder × Dynamic.Value)}
    {values : List Value}
    (represented : TypedValueRep compilation.checked.catalog compilation.signatures expected sourceValue value)
    (matched : Dynamic.PatternMatches context pattern sourceValue bindings)
    (bindingsRepresented : DataPatternLeaves.BindingsRep compilation.checked.catalog compiled.bindings bindings values) :
    BindingsRep compilation.checked.catalog compilation.signatures compiled.bindings bindings values := by
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context signatures _ _ _ root
  cases matched with
  | intro matchedSource instructionMatch =>
    have arityEq := Dynamic.MatchPatternSourceRepresents.rootArity_eq sourceRep matchedSource
    subst arityEq
    subst instructions
    obtain ⟨typedValues, _, typed⟩ := Tree.binding_types tree _ _ _ _ represented instructionMatch
    have same := bindings_core_unique typed.erase bindingsRepresented
    exact same ▸ typed

end Solcore.SourceSemantics.CoreLowering.DataPatternBindings

import Solcore.SourceSemantics.CoreLowering.DataEqualityInstalled

/-! Lookup facts extracted from the actual comparator generator. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataEqualityGeneration
open Core Frontend SourceCoreDataEquality

theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : first >>= next = .ok value) : ∃ input, first = .ok input ∧ next input = .ok value := by
  cases first <;> simp_all [bind, Except.bind]

theorem mapM_lookup {α β ε : Type} (function : α → Except ε β) {inputs : List α} {outputs : List β}
    (accepted : inputs.mapM function = .ok outputs) {index : Nat} {input : α}
    (selected : inputs[index]? = some input) :
    ∃ output, outputs[index]? = some output ∧ function input = .ok output := by
  induction inputs generalizing outputs index with
  | nil => simp at selected
  | cons head tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨value, generated, accepted⟩ := bind_ok accepted
    obtain ⟨values, rest, accepted⟩ := bind_ok accepted
    simp only [pure, Except.pure, Except.ok.injEq] at accepted
    subst outputs
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at selected; subst input; exact ⟨value, rfl, generated⟩
    | succ index => exact ih rest selected

theorem helperBodies_lookup {fuel : Nat} {catalog : Catalog} {bodies : List Expr}
    (generated : helperBodies fuel catalog = .ok bodies) {index : Nat}
    (bound : index < catalog.entries.length) :
    ∃ body, bodies[index]? = some body ∧ helperBody fuel catalog ⟨index⟩ = .ok body := by
  exact mapM_lookup (fun (row : SourceCoreDataCatalog.Entry × Nat) => helperBody fuel catalog ⟨row.2⟩)
    generated (input := (catalog.entries[index], index))
    (by simp [List.getElem?_zipIdx, List.getElem?_eq_getElem bound])

theorem nominalBody_branches {fuel : Nat} {catalog : Catalog} {id : DataTypeId}
    {payloads : List Ty} {body : Expr} (generated : nominalBody fuel catalog id payloads = .ok body)
    {leftIndex rightIndex : Nat} {leftType rightType : Ty}
    (leftSelected : payloads[leftIndex]? = some leftType)
    (rightSelected : payloads[rightIndex]? = some rightType) :
    ∃ branches rightBranches branch,
      body = .matchData id .bool (.first (.var 0)) branches ∧
      branches[leftIndex]? = some (.matchData id .bool (.second (.var 1)) rightBranches) ∧
      rightBranches[rightIndex]? = some branch ∧
      (if leftIndex = rightIndex then compareType fuel catalog 3 leftType (.var 1) (.var 0)
       else .ok (.bool false)) = .ok branch := by
  unfold nominalBody at generated
  obtain ⟨branches, generatedBranches, generated⟩ := bind_ok generated
  simp only [pure, Except.pure, Except.ok.injEq] at generated
  subst body
  obtain ⟨leftBranch, selectedBranch, generatedLeft⟩ := mapM_lookup _ generatedBranches
    (index := leftIndex) (input := (leftType, leftIndex)) (by simp [List.getElem?_zipIdx, leftSelected])
  obtain ⟨rightBranches, generatedRight, generatedLeft⟩ := bind_ok generatedLeft
  simp only [pure, Except.pure, Except.ok.injEq] at generatedLeft
  subst leftBranch
  obtain ⟨branch, selectedRight, generatedBranch⟩ := mapM_lookup _ generatedRight
    (index := rightIndex) (input := (rightType, rightIndex)) (by simp [List.getElem?_zipIdx, rightSelected])
  exact ⟨branches, rightBranches, branch, rfl, selectedBranch, selectedRight, generatedBranch⟩

theorem rename_weaken (expression : Expr) (mapping : Renaming) :
    (expression.weakenAt 0).rename mapping.lift = (expression.rename mapping).weakenAt 0 := by
  rw [← Expr.rename_insertion, ← Expr.rename_insertion, Expr.rename_comp, Expr.rename_comp]
  congr 1

theorem functionEqual_rename (left right : Expr) (mapping : Renaming) :
    (functionEqual left right).rename mapping = functionEqual (left.rename mapping) (right.rename mapping) := by
  simp [functionEqual, Expr.rename, rename_weaken, TaggedFunction.equalBody, Renaming.lift]

theorem invoke_rename (reference left right : Expr) (mapping : Renaming) :
    (invoke reference left right).rename mapping = invoke (reference.rename mapping) (left.rename mapping) (right.rename mapping) := by
  simp [invoke, Expr.rename, rename_weaken, Renaming.lift]

theorem renameList_lookup {branches : List Expr} {index : Nat} {branch : Expr}
    (selected : branches[index]? = some branch) (mapping : Renaming) :
    (Expr.renameList branches mapping)[index]? = some (branch.rename mapping) := by
  induction branches generalizing index with
  | nil => simp at selected
  | cons head tail ih => cases index with
    | zero => simpa [Expr.renameList] using congrArg (Option.map (·.rename mapping)) selected
    | succ index => exact ih selected

theorem nominal_compareType {catalog : Catalog} {id : DataTypeId} {entry : SourceCoreDataCatalog.Entry}
    (selected : catalog.entries[id.index]? = some entry)
    {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
    (nominal : SourceCoreDataCatalog.nominalParts entry.sourceType = some (declaration, arguments))
    {fuel depth : Nat} {left right compiled : Expr}
    (accepted : compareType fuel catalog depth (.namedData id) left right = .ok compiled) :
    compiled = invoke (.var (referenceIndex catalog depth id)) left right := by
  cases fuel with
  | zero => simp [compareType] at accepted
  | succ fuel =>
    cases kind : entry.sourceType <;>
      simp only [compareType, selected, kind, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
    all_goals try exact accepted.symm
    all_goals simp [kind, SourceCoreDataCatalog.nominalParts] at nominal

theorem nominal_helperBody {catalog : Catalog} {id : DataTypeId} {entry : SourceCoreDataCatalog.Entry}
    (selected : catalog.entries[id.index]? = some entry)
    {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
    (nominal : SourceCoreDataCatalog.nominalParts entry.sourceType = some (declaration, arguments))
    {fuel : Nat} {body : Expr} (accepted : helperBody fuel catalog id = .ok body) :
    ∃ definition, entry.definition = some definition ∧
      nominalBody fuel catalog id definition.constructorPayloadTypes = .ok body := by
  have next : (match entry.definition with
      | some definition => nominalBody fuel catalog id definition.constructorPayloadTypes
      | none => .error (.missingDefinition id)) = .ok body := by
    cases kind : entry.sourceType <;>
      simp only [helperBody, selected, kind, bind, Except.bind, pure, Except.pure] at accepted
    all_goals try exact accepted
    all_goals simp [kind, SourceCoreDataCatalog.nominalParts] at nominal
  cases found : entry.definition with
  | none => simp [found] at next
  | some definition => exact ⟨definition, rfl, by simpa [found] using next⟩

theorem registered_payload {catalog : Catalog} {id : DataTypeId} {entry : SourceCoreDataCatalog.Entry}
    (selected : catalog.entries[id.index]? = some entry) {definition : DataDefinition}
    (definitionSelected : entry.definition = some definition) {index : Nat} {payloadType : Ty}
    (registered : catalog.definitions.lookupConstructorPayloadType? ⟨id, index⟩ = some payloadType) :
    definition.constructorPayloadTypes[index]? = some payloadType := by
  simpa [SourceCoreDataCatalog.Catalog.definitions, DataEnvironment.lookupConstructorPayloadType?,
    DataEnvironment.lookupDataType?, selected, definitionSelected] using registered

end Solcore.SourceSemantics.CoreLowering.DataEqualityGeneration

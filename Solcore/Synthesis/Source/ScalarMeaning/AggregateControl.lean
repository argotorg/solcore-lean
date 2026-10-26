import Solcore.Synthesis.Source.ScalarMeaning.AggregatePreservation

/-! Simulation lemmas for the binding and control forms of the actual
`AggregateRenderer.render`, and the structural induction over Core
expressions. A Core `case` binds its payload before every existing local; the
source binds it in the selected case scope under a fresh `sc_p<n>` name. A
projection matches the pair once and assigns the picked component to a fresh
temporary. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target)
open Solcore.Synthesis.Source.AggregateRenderer (Binding)
open Solcore.Synthesis.Core.Aggregates (Local initializerKind? infer?)

/-! ### Zero values -/

/-- The value of an `if` or `case` result before a branch assigns it. -/
def azeroValue : ATarget → Value
  | .bool => .bool false
  | .wordPair => .pair 0 0
  | .wordSum => .inl 0
  | _ => .word 0

theorem azero_eval (context : Context) (frames : Frames) (target : ATarget) :
    (azero target).eval context frames = some (azeroValue target) := by
  cases target <;> simp [azero, azeroValue, Expr.eval, Evm.modulus]

theorem azeroValue_admits (target : ATarget) :
    target.localType.admits (azeroValue target) = true := by
  cases target <;> rfl

theorem azero_identifiers (target : ATarget) : (azero target).identifiers = [] := by
  cases target <;> rfl

theorem AValue.sameType_zero {target : ATarget} {core : CoreValue} {value : Value}
    (represents : AValue target core value) : value.sameType (azeroValue target) = true := by
  cases target
  case word =>
    obtain ⟨_, _, rfl⟩ := represents
    rfl
  case bool =>
    obtain ⟨_, _, rfl⟩ := represents
    rfl
  case unit => exact represents.elim
  case wordPair =>
    obtain ⟨_, _, _, rfl⟩ := represents
    rfl
  case wordSum =>
    rcases represents with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl

theorem not_mem_names_nil (name : String) : name ∉ Scope.names [] := by
  simp [Scope.names]

theorem payloadTemp_inj {first second : Nat} :
    payloadTemp first = payloadTemp second ↔ first = second :=
  ⟨payloadTemp_injective, fun same => same ▸ rfl⟩

/-! ### Frames -/

/-- A case scope that binds a fresh payload name extends the agreement by
that payload. -/
theorem ABindingsAgree.payload {scope : Scope} {outer : Frames} {bindings : List Binding}
    {environment : Solcore.Core.Environment} {store : Solcore.Core.Store}
    (agree : ABindingsAgree (scope :: outer) bindings environment store) {name : String}
    (absent : ∀ index found, anameAt bindings index = some found → found ≠ name)
    (word : Solcore.Core.Word) :
    ABindingsAgree ([(name, .word word.val)] :: scope :: outer) (.word name :: bindings)
      (.word word :: environment) store := by
  refine (agree.enter [(name, .word word.val)] fun index found named mem => ?_).cons ?_
  · simp only [Scope.names, List.map_cons, List.map_nil, List.mem_singleton] at mem
    exact absent index found named mem
  · exact ⟨.word word.val, by simp [Frames.lookup, Scope.get?], word, rfl, rfl⟩

theorem ABindingsAgree.write {frames frames' : Frames} {bindings : List Binding}
    {environment : Solcore.Core.Environment} {store store' : Solcore.Core.Store}
    (agree : ABindingsAgree frames bindings environment store)
    (namesDistinct : ANamesDistinct bindings)
    (cellsDistinct : ACellsDistinct bindings environment) {index location : Nat}
    {name : String} {elementType : Solcore.Core.Ty} {word : Solcore.Core.Word}
    (found : bindings[index]? = some (Binding.cellWord name))
    (inEnvironment : environment[index]? = some (.cellRef elementType location))
    (written : store.write? location (.word word) = some store')
    (lookups : ∀ other, frames'.lookup other =
      if name = other then some (.word word.val) else frames.lookup other) :
    ABindingsAgree frames' bindings environment store' := by
  intro position binding foundBinding
  obtain ⟨core, inEnvironment', holds⟩ := agree position binding foundBinding
  refine ⟨core, inEnvironment', ?_⟩
  by_cases same : position = index
  · subst same
    rw [found] at foundBinding
    cases foundBinding
    rw [inEnvironment] at inEnvironment'
    cases inEnvironment'
    exact ⟨elementType, location, word, rfl, Solcore.Core.Store.write?_reads_written written,
      by rw [lookups name, if_pos rfl]⟩
  · have otherName : ∀ found, abindingName? binding = some found → name ≠ found := by
      intro found' named sameName
      subst sameName
      exact same (namesDistinct position index name
        (by rw [anameAt_of_getElem? foundBinding]; exact named)
        (by rw [anameAt_of_getElem? found]; rfl))
    cases binding with
    | word other =>
        show ARepresents .word core (frames'.lookup other)
        rw [lookups other, if_neg (otherName other rfl)]
        exact holds
    | bool other =>
        show ARepresents .bool core (frames'.lookup other)
        rw [lookups other, if_neg (otherName other rfl)]
        exact holds
    | wordPair other =>
        show ARepresents .wordPair core (frames'.lookup other)
        rw [lookups other, if_neg (otherName other rfl)]
        exact holds
    | wordSum other =>
        show ARepresents .wordSum core (frames'.lookup other)
        rw [lookups other, if_neg (otherName other rfl)]
        exact holds
    | unit => exact holds
    | cellWord other =>
        obtain ⟨elementType', location', value, rfl, read, lookup⟩ := holds
        have otherLocation : location' ≠ location := by
          intro sameLocation
          subst sameLocation
          exact same (cellsDistinct position index location' ⟨⟨other, foundBinding⟩, _,
            inEnvironment'⟩ ⟨⟨name, found⟩, _, inEnvironment⟩)
        exact ⟨elementType', location', value, rfl,
          by rw [Solcore.Core.Store.write?_preserves_other written otherLocation]; exact read,
          by rw [lookups other, if_neg (otherName other rfl)]; exact lookup⟩

section

variable {admits : Context → Prop}

/-! ### Branch and case bodies -/

/-- A branch or case body of Unit type runs in a block scope that starts as
`armScope` and is discarded afterwards. A case body's bindings extend the
enclosing bindings by the payload; an `if` body keeps them. -/
theorem aarm_unit {expression : CoreExpr} {functions : List String}
    {bindings bodyBindings : List Binding}
    {environment bodyEnvironment : Solcore.Core.Environment} {low high : Nat}
    {statements : List Stmt} {valueName : Option String} {context : Context}
    {store : Solcore.Core.Store} {armScope scope : Scope} {outer : Frames}
    (simulates : ASimulates admits expression .unit functions bodyBindings low high statements
      valueName)
    (fresh : ANamesFresh bindings low) (admitted : admits context)
    (entryAgree : ABindingsAgree (armScope :: scope :: outer) bodyBindings bodyEnvironment store)
    (entryCells : ACellsDistinct bodyBindings bodyEnvironment)
    (entryLength : bodyBindings.length ≤ bodyEnvironment.length)
    (entryFunctions : MFunctionsAgree context functions
      (bodyEnvironment.drop bodyBindings.length))
    (exitAgree : ∀ (frames : Frames) (store' : Solcore.Core.Store),
      ABindingsAgree frames bodyBindings bodyEnvironment store' →
        ABindingsAgree frames bindings environment store')
    (exitFrame : ∀ store' : Solcore.Core.Store,
      AStoreFrame bodyBindings bodyEnvironment store store' →
        AStoreFrame bindings environment store store')
    (exitCells : ∀ name, (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
      ∀ index : Nat, bodyBindings[index]? ≠ some (Binding.cellWord name))
    (armOutside : ∀ index name, anameAt bindings index = some name → name ∉ armScope.names) :
    ∃ (store' : Solcore.Core.Store) (top scope' : Scope) (outer' : Frames),
      Solcore.Core.Evaluates bodyEnvironment store expression.toCore .unit store' ∧
      Stmt.execList context (armScope :: scope :: outer) statements =
        some (top :: scope' :: outer') ∧
      ABindingsAgree (scope' :: outer') bindings environment store' ∧
      AStoreFrame bindings environment store store' ∧
      scope'.names = scope.names ∧ Frames.shape outer' = Frames.shape outer ∧
      ∀ name, ¬ ATempIn low high name → name ∉ armScope.names →
        (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
        Frames.lookup (scope' :: outer') name = Frames.lookup (scope :: outer) name := by
  obtain ⟨coreValue, store', top, frames, added, evaluates, represents, exec, agree₁, frame, keeps,
    shape, topNames, addedTemp⟩ :=
    simulates context bodyEnvironment store armScope (scope :: outer) admitted entryAgree
      entryCells entryLength entryFunctions
  have unitCore : coreValue = .unit := represents
  subst unitCore
  obtain ⟨scope', outer', rfl, scopeNames, outerShape⟩ := frames_after_block shape
  have absent : ∀ name, ¬ ATempIn low high name → name ∉ armScope.names → name ∉ top.names := by
    intro name notTemp notArm mem
    rw [topNames] at mem
    rcases List.mem_append.mp mem with mem | mem
    · exact notTemp (addedTemp name mem)
    · exact notArm mem
  refine ⟨store', top, scope', outer', evaluates, exec, ?_, exitFrame store' frame, scopeNames,
    outerShape, ?_⟩
  · exact (exitAgree _ store' agree₁).leave fun index name named =>
      absent name (not_aTempIn_of_fresh (fresh index name named) (Nat.le_refl _))
        (armOutside index name named)
  · intro name notTemp notArm notCell
    rw [← Frames.lookup_cons_of_not_mem (scope' :: outer') (absent name notTemp notArm),
      keeps name notTemp (exitCells name notCell),
      Frames.lookup_cons_of_not_mem (scope :: outer) notArm]

/-- A branch or case body of a value type ends by assigning its value to the
result declared before the `if` or `match`. -/
theorem aarm_value {expression : CoreExpr} {target : ATarget} {functions : List String}
    {bindings bodyBindings : List Binding}
    {environment bodyEnvironment : Solcore.Core.Environment} {low high : Nat}
    {statements : List Stmt} {valueName result : String} {context : Context}
    {store : Solcore.Core.Store} {armScope scope : Scope} {outer : Frames}
    (valued : target ≠ .unit)
    (simulates : ASimulates admits expression target functions bodyBindings low high statements
      (some valueName))
    (fresh : ANamesFresh bindings low) (admitted : admits context)
    (entryAgree : ABindingsAgree (armScope :: scope :: outer) bodyBindings bodyEnvironment store)
    (entryCells : ACellsDistinct bodyBindings bodyEnvironment)
    (entryLength : bodyBindings.length ≤ bodyEnvironment.length)
    (entryFunctions : MFunctionsAgree context functions
      (bodyEnvironment.drop bodyBindings.length))
    (exitAgree : ∀ (frames : Frames) (store' : Solcore.Core.Store),
      ABindingsAgree frames bodyBindings bodyEnvironment store' →
        ABindingsAgree frames bindings environment store')
    (exitFrame : ∀ store' : Solcore.Core.Store,
      AStoreFrame bodyBindings bodyEnvironment store store' →
        AStoreFrame bindings environment store store')
    (exitCells : ∀ name, (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
      ∀ index : Nat, bodyBindings[index]? ≠ some (Binding.cellWord name))
    (armOutside : ∀ index name, anameAt bindings index = some name → name ∉ armScope.names)
    (resultOutside : ¬ ATempIn low high result) (resultNotArm : result ∉ armScope.names)
    (resultNotCell : ∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord result))
    (resultNotBinding : ∀ index found, anameAt bindings index = some found → found ≠ result)
    (declared : Frames.lookup (scope :: outer) result = some (azeroValue target)) :
    ∃ (coreValue : CoreValue) (value : Value) (store' : Solcore.Core.Store) (top scope' : Scope)
      (outer' : Frames),
      Solcore.Core.Evaluates bodyEnvironment store expression.toCore coreValue store' ∧
      AValue target coreValue value ∧
      Stmt.execList context (armScope :: scope :: outer)
        (statements ++ [.assign result (.name valueName)]) = some (top :: scope' :: outer') ∧
      ABindingsAgree (scope' :: outer') bindings environment store' ∧
      AStoreFrame bindings environment store store' ∧
      scope'.names = scope.names ∧ Frames.shape outer' = Frames.shape outer ∧
      ∀ name, ¬ ATempIn low high name → name ∉ armScope.names →
        (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
        Frames.lookup (scope' :: outer') name =
          if result = name then some value else Frames.lookup (scope :: outer) name := by
  obtain ⟨coreValue, store', top₁, frames₁, added, evaluates, represents, exec, agree₁, frame,
    keeps, shape, topNames, addedTemp⟩ :=
    simulates context bodyEnvironment store armScope (scope :: outer) admitted entryAgree
      entryCells entryLength entryFunctions
  simp only [Option.bind_some] at represents
  obtain ⟨value, lookupValue, represents'⟩ := represents.value valued
  have resultFound : Frames.lookup (top₁ :: frames₁) result = some (azeroValue target) := by
    rw [keeps result resultOutside (exitCells result resultNotCell),
      Frames.lookup_cons_of_not_mem (scope :: outer) resultNotArm]
    exact declared
  obtain ⟨frames₂, assigned, shape₂, lookups⟩ :=
    Frames.assign_spec (frames := top₁ :: frames₁) value resultFound
  have shapeCons : Frames.shape frames₂ = top₁.names :: Frames.shape (scope :: outer) := by
    rw [shape₂]
    simp only [Frames.shape, List.map_cons] at shape ⊢
    rw [shape]
  obtain ⟨top₂, frames₃, rfl, topNames₂, shape₃⟩ := frames_after_block (outer := scope :: outer)
    (scope := top₁) (frames := frames₂) (by rw [shapeCons]; rfl)
  obtain ⟨scope', outer', rfl, scopeNames, outerShape⟩ := frames_after_block shape₃
  have absent : ∀ name, ¬ ATempIn low high name → name ∉ armScope.names →
      name ∉ top₂.names := by
    intro name notTemp notArm mem
    rw [topNames₂, topNames] at mem
    rcases List.mem_append.mp mem with mem | mem
    · exact notTemp (addedTemp name mem)
    · exact notArm mem
  refine ⟨coreValue, value, store', top₂, scope', outer', evaluates, represents', ?_, ?_,
    exitFrame store' frame, scopeNames, outerShape, ?_⟩
  · rw [Stmt.execList_append, exec]
    simp [Stmt.execList, Stmt.exec, Expr.eval, lookupValue, resultFound,
      represents'.sameType_zero, assigned]
  · refine (exitAgree _ store' agree₁).transfer (fun index found named => ?_) (fun _ _ _ => rfl)
    have notTemp := not_aTempIn_of_fresh (last := high) (fresh index found named)
      (Nat.le_refl _)
    rw [← Frames.lookup_cons_of_not_mem (scope' :: outer')
        (absent found notTemp (armOutside index found named)), lookups found,
      if_neg (resultNotBinding index found named).symm]
  · intro name notTemp notArm notCell
    rw [← Frames.lookup_cons_of_not_mem (scope' :: outer') (absent name notTemp notArm),
      lookups name, keeps name notTemp (exitCells name notCell),
      Frames.lookup_cons_of_not_mem (scope :: outer) notArm]

/-! ### Local bindings -/

/-- A `let` that allocates a Core cell declares an `sc_c<n>` local. -/
theorem aRenderIH_newCellLet {inner body : CoreExpr} (innerIH : ARenderIH inner)
    (bodyIH : ARenderIH body) : ARenderIH (.letE (.newCell .word inner) body) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨kind, initializerKind, bodyKind, _⟩ := AggregateKinds.letE accepted
  obtain ⟨rfl, innerKind⟩ := AggregateKinds.newCell initializerKind
  obtain ⟨initial, value, rest, initialEquation, valueFound, restEquation, rfl⟩ :=
    AggregateEquations.newCellLet_ok equation
  obtain ⟨innerStatements, innerLines, innerLe, innerValue, innerNames, innerSimulates⟩ :=
    innerIH admits (AliasesReady.of_sub ready fun uses => by
        simp [AggregateRenderer.usesOpcodeAliases, uses])
      functions .word bindings indent first initial innerKind initialEquation fresh distinct
  have cellTemp' : ∀ last, initial.nextId < last →
      ATempIn first last (cellTemp initial.nextId) :=
    fun _ lt => aTempIn_cellTemp innerLe lt
  have bodyFresh : ANamesFresh (.cellWord (cellTemp initial.nextId) :: bindings)
      (initial.nextId + 1) := by
    refine fresh.cons (Nat.le_succ_of_le innerLe) fun name same => ?_
    cases same
    exact cellTemp_fresh _
  have bodyDistinct : ANamesDistinct (.cellWord (cellTemp initial.nextId) :: bindings) :=
    distinct.cons fresh fun name same => by
      cases same
      exact ⟨initial.nextId, Or.inr (Or.inl rfl), innerLe⟩
  obtain ⟨bodyStatements, bodyLines, bodyLe, bodyValue, bodyNames, bodySimulates⟩ :=
    bodyIH admits (AliasesReady.of_sub ready fun uses => by
        simp [AggregateRenderer.usesOpcodeAliases, uses])
      functions target (.cellWord (cellTemp initial.nextId) :: bindings) indent
      (initial.nextId + 1) rest bodyKind restEquation bodyFresh bodyDistinct
  refine ⟨innerStatements ++ [.letDecl (cellTemp initial.nextId) .word (.name value)] ++
      bodyStatements, ?_, by dsimp only; omega, ?_, ?_, ?_⟩
  · simp only [Stmt.listLines_append, innerLines, bodyLines, Stmt.listLines, List.append_nil]
  · intro name same
    rcases bodyValue name same with ⟨index, kind, valued, found⟩ | ⟨index, rfl, lower, upper⟩
    · cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          exact absurd found.symm (valueBinding_ne_cell _ _)
      | succ index => exact Or.inl ⟨index, kind, valued, by simpa using found⟩
    · exact Or.inr ⟨index, rfl, by omega, upper⟩
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at mem
    rcases mem with (mem | same | same) | mem
    · exact (innerNames name mem).mono (Nat.le_refl _) (by dsimp only; omega)
    · subst same
      exact Or.inr (Or.inr (Or.inl (cellTemp' _ (by dsimp only; omega))))
    · subst same
      exact (innerValue name valueFound).uses.mono (Nat.le_refl _) (by dsimp only; omega)
    · exact (bodyNames name mem).of_cons
        (fun found same => by cases same; exact cellTemp' _ (by omega))
        (Nat.le_succ_of_le innerLe)
  · dsimp only
    intro context environment store scope outer admitted agree distinctCells lengthOk functionsOk
    obtain ⟨innerCore, store₁, scope₁, outer₁, added₁, innerEvaluates, innerRepresents,
      innerExec, agree₁, frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
      innerSimulates context environment store scope outer admitted agree distinctCells
        lengthOk functionsOk
    rw [valueFound, Option.bind_some] at innerRepresents
    obtain ⟨_, lookupValue, word, rfl, rfl⟩ := innerRepresents
    have oldRead : ∀ other, other < store₁.length →
        (store₁ ++ [Solcore.Core.Value.word word]).read? other = store₁.read? other := by
      intro other lt
      simp [Solcore.Core.Store.read?, List.getElem?_append_left lt]
    have cellNew : ∀ index location, ACellAt bindings environment index location →
        location ≠ store₁.length :=
      fun _ _ isCell same => absurd (agree₁.cell_lt isCell) (by omega)
    have bodyAgree : ABindingsAgree (((cellTemp initial.nextId, .word word.val) :: scope₁) ::
        outer₁)
        (.cellWord (cellTemp initial.nextId) :: bindings)
        (.cellRef (Solcore.Core.Wire.Ty.toCore .word) store₁.length :: environment)
        (store₁ ++ [.word word]) := by
      refine ABindingsAgree.cons ?_ ⟨_, store₁.length, word, rfl, by
        simp [Solcore.Core.Store.read?], by simp [Frames.lookup_declared]⟩
      exact (agree₁.declare (fresh.ne_temp (cellTemp' _ (Nat.lt_succ_self _))) _).transfer
        (fun _ _ _ => rfl) fun _ location isCell => oldRead location (agree₁.cell_lt isCell)
    have bodyCells : ACellsDistinct (.cellWord (cellTemp initial.nextId) :: bindings)
        (.cellRef (Solcore.Core.Wire.Ty.toCore .word) store₁.length :: environment) := by
      have headCell : ∀ location, ACellAt (.cellWord (cellTemp initial.nextId) :: bindings)
          (.cellRef (Solcore.Core.Wire.Ty.toCore .word) store₁.length :: environment) 0
            location → location = store₁.length := by
        intro location isCell
        obtain ⟨_, elementType, inEnvironment⟩ := isCell
        simp only [List.getElem?_cons_zero, Option.some.injEq,
          Solcore.Core.Value.cellRef.injEq] at inEnvironment
        exact inEnvironment.2.symm
      intro one two location cellOne cellTwo
      cases one with
      | zero =>
          cases two with
          | zero => rfl
          | succ two =>
              exact absurd (headCell location cellOne) (cellNew two location cellTwo.of_cons)
      | succ one =>
          cases two with
          | zero =>
              exact absurd (headCell location cellTwo) (cellNew one location cellOne.of_cons)
          | succ two =>
              exact congrArg (· + 1) (distinctCells one two location cellOne.of_cons
                cellTwo.of_cons)
    obtain ⟨bodyCore, store₂, scope₂, outer₂, added₂, bodyEvaluates, bodyRepresents, bodyExec,
      agree₂, frame₂, keeps₂, shape₂, names₂, addedTemp₂⟩ :=
      bodySimulates context _ (store₁ ++ [.word word])
        ((cellTemp initial.nextId, .word word.val) :: scope₁) outer₁
        admitted bodyAgree bodyCells (by simp; omega) (by simpa using functionsOk)
    have cellOutside : ∀ name, ¬ ATempIn first rest.nextId name →
        cellTemp initial.nextId ≠ name :=
      fun name notTemp same => notTemp (same ▸ cellTemp' _ (by omega))
    refine ⟨bodyCore, store₂, scope₂, outer₂, added₂ ++ cellTemp initial.nextId :: added₁, ?_,
      bodyRepresents, ?_, agree₂.tail, ?_, ?_, shape₂.trans shape₁, ?_, ?_⟩
    · simp only [Solcore.Core.Wire.Expr.toCore]
      exact .letE (.newCell innerEvaluates) bodyEvaluates
    · rw [Stmt.execList_append, Stmt.execList_append, innerExec]
      simp [Stmt.execList, Stmt.exec, Expr.eval, lookupValue, LocalType.admits, Frames.declare,
        bodyExec]
    · refine ⟨by have := frame₁.1; have := frame₂.1; simp at *; omega,
        fun other lt notCell => ?_⟩
      have lt₁ : other < store₁.length := Nat.lt_of_lt_of_le lt frame₁.1
      have notBodyCell : ∀ index, ¬ ACellAt (.cellWord (cellTemp initial.nextId) :: bindings)
          (.cellRef (Solcore.Core.Wire.Ty.toCore .word) store₁.length :: environment) index
          other := by
        intro index isCell
        cases index with
        | zero =>
            obtain ⟨_, elementType, inEnvironment⟩ := isCell
            simp only [List.getElem?_cons_zero, Option.some.injEq,
              Solcore.Core.Value.cellRef.injEq] at inEnvironment
            have same : (store₁.length : Nat) = other := inEnvironment.2
            omega
        | succ index => exact notCell index isCell.of_cons
      rw [frame₂.2 other (by simp; omega) notBodyCell, oldRead other lt₁,
        frame₁.2 other lt notCell]
    · intro name notTemp notCell
      rw [keeps₂ name (fun temp => notTemp (aTempIn_mono temp (by omega) (Nat.le_refl _)))
          (fun index found => ?_),
        Frames.lookup_declared, if_neg (cellOutside name notTemp),
        keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) (by omega)))
          notCell]
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq,
            Binding.cellWord.injEq] at found
          exact cellOutside name notTemp found
      | succ index => exact notCell index (by simpa using found)
    · rw [names₂]
      show added₂ ++ cellTemp initial.nextId :: scope₁.names =
        (added₂ ++ cellTemp initial.nextId :: added₁) ++ scope.names
      rw [names₁]
      simp
    · intro name mem
      simp only [List.mem_append, List.mem_cons] at mem
      rcases mem with mem | same | mem
      · exact aTempIn_mono (addedTemp₂ name mem) (by omega) (Nat.le_refl _)
      · exact same ▸ cellTemp' _ (by omega)
      · exact aTempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) (by omega)

/-- A `let` of a Word, Boolean, pair or sum value copies it to a fresh
temporary, which the body sees as a value binding. -/
theorem aletValue_spec {initializer body : CoreExpr} {kindTarget target : ATarget}
    {functions : List String} {bindings : List Binding} {indent first : Nat}
    {initial rest : ARendered} {value : String}
    (unitKind : ¬ kindTarget = .unit) (fresh : ANamesFresh bindings first)
    (initSpec : ARenderSpec admits initializer kindTarget functions bindings indent first initial)
    (valueFound : initial.value = some value)
    (bodySpec : ARenderSpec admits body target functions
      (valueBinding kindTarget (temporary initial.nextId) :: bindings) indent
      (initial.nextId + 1) rest) :
    ARenderSpec admits (.letE initializer body) target functions bindings indent first
      ⟨initial.lines ++ Stmt.lines indent (.letDecl (temporary initial.nextId)
          (ATarget.localType kindTarget) (.name value)) ++ rest.lines,
        rest.value, rest.nextId⟩ := by
  obtain ⟨initStatements, initLines, initLe, initValue, initNames, initSimulates⟩ := initSpec
  obtain ⟨bodyStatements, bodyLines, bodyLe, bodyValue, bodyNames, bodySimulates⟩ := bodySpec
  have bound : ∀ last, initial.nextId < last →
      ATempIn first last (temporary initial.nextId) :=
    fun _ lt => aTempIn_temporary initLe lt
  refine ⟨initStatements ++ [.letDecl (temporary initial.nextId) (ATarget.localType kindTarget)
    (.name value)] ++ bodyStatements, ?_, by dsimp only; omega, ?_, ?_, ?_⟩
  · simp only [Stmt.listLines_append, initLines, bodyLines, Stmt.listLines, List.append_nil]
  · intro name same
    rcases (bodyValue name same).mono (Nat.le_succ_of_le initLe) (Nat.le_refl _) with
      ⟨index, kind, valued, found⟩ | ⟨index, rfl, lower, upper⟩
    · cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          have sameName : name = temporary initial.nextId := by
            have := congrArg abindingName? found
            rw [valueBinding_name unitKind, valueBinding_name valued] at this
            exact (Option.some.inj this).symm
          subst sameName
          exact Or.inr ⟨initial.nextId, rfl, initLe, by dsimp only; omega⟩
      | succ index => exact Or.inl ⟨index, kind, valued, by simpa using found⟩
    · exact Or.inr ⟨index, rfl, lower, upper⟩
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at mem
    rcases mem with (mem | same | same) | mem
    · exact (initNames name mem).mono (Nat.le_refl _) (by dsimp only; omega)
    · subst same
      exact Or.inr (Or.inr (Or.inl (bound _ (by dsimp only; omega))))
    · subst same
      exact (initValue name valueFound).uses.mono (Nat.le_refl _) (by dsimp only; omega)
    · exact (bodyNames name mem).of_cons
        (fun found same => by
          rw [valueBinding_name unitKind] at same
          cases same
          exact bound _ (by omega))
        (Nat.le_succ_of_le initLe)
  · dsimp only
    intro context environment store scope outer admitted agree distinctCells lengthOk
      functionsOk
    obtain ⟨initCore, store₁, scope₁, outer₁, added₁, initEvaluates, initRepresents, initExec,
      agree₁, frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
      initSimulates context environment store scope outer admitted agree distinctCells
        lengthOk functionsOk
    rw [valueFound, Option.bind_some] at initRepresents
    obtain ⟨source, lookupValue, represents⟩ := initRepresents.value unitKind
    have bodyAgree : ABindingsAgree (((temporary initial.nextId, source) :: scope₁) :: outer₁)
        (valueBinding kindTarget (temporary initial.nextId) :: bindings)
        (initCore :: environment) store₁ := by
      refine (agree₁.declare (fresh.ne_temp (bound _ (Nat.lt_succ_self _))) source).cons ?_
      rw [valueBinding_holds unitKind]
      simp only [Frames.lookup_declared, if_pos]
      exact ARepresents.of_value represents
    have notCellBinding : ∀ name, valueBinding kindTarget (temporary initial.nextId) ≠
        .cellWord name := fun name => valueBinding_ne_cell _ _
    obtain ⟨bodyCore, store₂, scope₂, outer₂, added₂, bodyEvaluates, bodyRepresents, bodyExec,
      agree₂, frame₂, keeps₂, shape₂, names₂, addedTemp₂⟩ :=
      bodySimulates context (initCore :: environment) store₁
        ((temporary initial.nextId, source) :: scope₁) outer₁ admitted bodyAgree
        (distinctCells.cons_value notCellBinding) (by simp; omega) (by simpa using functionsOk)
    have outside : ∀ name, ¬ ATempIn first rest.nextId name →
        temporary initial.nextId ≠ name :=
      fun name notTemp same => notTemp (same ▸ bound _ (by omega))
    refine ⟨bodyCore, store₂, scope₂, outer₂, added₂ ++ temporary initial.nextId :: added₁,
      ?_, bodyRepresents, ?_, agree₂.tail, ?_, ?_, shape₂.trans shape₁, ?_, ?_⟩
    · simp only [Solcore.Core.Wire.Expr.toCore]
      exact .letE initEvaluates bodyEvaluates
    · rw [Stmt.execList_append, Stmt.execList_append, initExec]
      simp [Stmt.execList, Stmt.exec, Expr.eval, lookupValue, represents.admits,
        Frames.declare, bodyExec]
    · exact frame₁.trans (frame₂.of_cons notCellBinding)
    · intro name notTemp notCell
      rw [keeps₂ name (fun temp => notTemp (aTempIn_mono temp (by omega) (Nat.le_refl _)))
          (fun index found => ?_),
        Frames.lookup_declared, if_neg (outside name notTemp),
        keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) (by omega)))
          notCell]
      cases index with
      | zero => exact notCellBinding name (by simpa using found)
      | succ index => exact notCell index (by simpa using found)
    · rw [names₂]
      show added₂ ++ temporary initial.nextId :: scope₁.names =
        (added₂ ++ temporary initial.nextId :: added₁) ++ scope.names
      rw [names₁]
      simp
    · intro name mem
      simp only [List.mem_append, List.mem_cons] at mem
      rcases mem with mem | same | mem
      · exact aTempIn_mono (addedTemp₂ name mem) (by omega) (Nat.le_refl _)
      · exact same ▸ bound _ (by omega)
      · exact aTempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) (by omega)

/-- A `let` of a Unit or value initializer. A Unit binding has no source name;
a Word, Boolean, pair or sum value is copied to a fresh immutable temporary. -/
theorem aRenderIH_letE {initializer body : CoreExpr}
    (notCell : ∀ inner, initializer = .newCell .word inner → False)
    (initializerIH : ARenderIH initializer) (bodyIH : ARenderIH body) :
    ARenderIH (.letE initializer body) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨kind, initializerKind, bodyKind, _⟩ := AggregateKinds.letE accepted
  obtain ⟨kindTarget, inferred⟩ := AggregateEquations.letE_infer notCell equation
  have sameKind : kind = kindTarget.toLocal := by
    have toLocal := AggregateKinds.infer_toLocal inferred
    rw [initializerKind] at toLocal
    exact Option.some.inj toLocal
  subst sameKind
  have initializerReady := AliasesReady.of_sub ready (sub := initializer) fun uses => by
    simp [AggregateRenderer.usesOpcodeAliases, uses]
  have bodyReady := AliasesReady.of_sub ready (sub := body) fun uses => by
    simp [AggregateRenderer.usesOpcodeAliases, uses]
  by_cases unitKind : kindTarget = .unit
  · subst unitKind
    obtain ⟨initial, rest, initialEquation, restEquation, rfl⟩ :=
      AggregateEquations.letE_unit_ok notCell inferred equation
    obtain ⟨initStatements, initLines, initLe, _, initNames, initSimulates⟩ :=
      initializerIH admits initializerReady functions .unit bindings indent first initial
        initializerKind initialEquation fresh distinct
    have bodyFresh : ANamesFresh (.unit :: bindings) initial.nextId :=
      fresh.cons initLe fun _ same => by cases same
    have bodyDistinct : ANamesDistinct (.unit :: bindings) :=
      distinct.cons fresh fun _ same => by cases same
    obtain ⟨bodyStatements, bodyLines, bodyLe, bodyValue, bodyNames, bodySimulates⟩ :=
      bodyIH admits bodyReady functions target (.unit :: bindings) indent initial.nextId rest
        bodyKind restEquation bodyFresh bodyDistinct
    refine ⟨initStatements ++ bodyStatements, ?_, by dsimp only; omega, ?_, ?_, ?_⟩
    · simp only [Stmt.listLines_append, initLines, bodyLines]
    · intro name same
      rcases bodyValue name same with ⟨index, kind, valued, found⟩ | ⟨index, rfl, lower, upper⟩
      · cases index with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            cases kind <;> first | exact absurd rfl valued | cases found
        | succ index => exact Or.inl ⟨index, kind, valued, by simpa using found⟩
      · exact Or.inr ⟨index, rfl, by omega, upper⟩
    · intro name mem
      rw [Stmt.listIdentifiers_append, List.mem_append] at mem
      rcases mem with mem | mem
      · exact (initNames name mem).mono (Nat.le_refl _) (by dsimp only; omega)
      · exact (bodyNames name mem).of_cons (fun _ same => by cases same) initLe
    · dsimp only
      intro context environment store scope outer admitted agree distinctCells lengthOk
        functionsOk
      obtain ⟨initCore, store₁, scope₁, outer₁, added₁, initEvaluates, initRepresents, initExec,
        agree₁, frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
        initSimulates context environment store scope outer admitted agree distinctCells
          lengthOk functionsOk
      have unitCore : initCore = .unit := initRepresents
      subst unitCore
      obtain ⟨bodyCore, store₂, scope₂, outer₂, added₂, bodyEvaluates, bodyRepresents, bodyExec,
        agree₂, frame₂, keeps₂, shape₂, names₂, addedTemp₂⟩ :=
        bodySimulates context (.unit :: environment) store₁ scope₁ outer₁ admitted
          (agree₁.cons rfl) (distinctCells.cons_value fun _ same => by cases same)
          (by simp; omega) (by simpa using functionsOk)
      refine ⟨bodyCore, store₂, scope₂, outer₂, added₂ ++ added₁, ?_, bodyRepresents, ?_,
        agree₂.tail, ?_, ?_, shape₂.trans shape₁, ?_, ?_⟩
      · simp only [Solcore.Core.Wire.Expr.toCore]
        exact .letE initEvaluates bodyEvaluates
      · rw [Stmt.execList_append, initExec]
        simpa using bodyExec
      · exact frame₁.trans (frame₂.of_cons fun _ same => by cases same)
      · intro name notTemp notCell
        rw [keeps₂ name (fun temp => notTemp (aTempIn_mono temp (by omega) (Nat.le_refl _)))
            (fun index found => ?_),
          keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) (by omega)))
            notCell]
        cases index with
        | zero => simp at found
        | succ index => exact notCell index (by simpa using found)
      · rw [names₂, names₁]
        simp
      · intro name mem
        rcases List.mem_append.mp mem with mem | mem
        · exact aTempIn_mono (addedTemp₂ name mem) (by omega) (Nat.le_refl _)
        · exact aTempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) (by omega)
  · obtain ⟨initial, value, rest, initialEquation, valueFound, restEquation, rfl⟩ :=
      AggregateEquations.letE_value_ok notCell unitKind inferred equation
    have initSpec := initializerIH admits initializerReady functions kindTarget bindings indent
      first initial initializerKind initialEquation fresh distinct
    have initLe := initSpec.le
    have bodyFresh : ANamesFresh (valueBinding kindTarget (temporary initial.nextId) :: bindings)
        (initial.nextId + 1) := by
      refine fresh.cons (Nat.le_succ_of_le initLe) fun name same => ?_
      rw [valueBinding_name unitKind] at same
      cases same
      exact temporary_fresh _
    have bodyDistinct : ANamesDistinct (valueBinding kindTarget (temporary initial.nextId) ::
        bindings) :=
      distinct.cons fresh fun name same => by
        rw [valueBinding_name unitKind] at same
        cases same
        exact ⟨initial.nextId, Or.inl rfl, initLe⟩
    have bodyKind' : initializerKind? ((valueBinding kindTarget (temporary initial.nextId) ::
        bindings).map Binding.kind) functions.length body = some target.toLocal := by
      simpa [valueBinding_kind unitKind] using bodyKind
    exact aletValue_spec unitKind fresh initSpec valueFound
      (bodyIH admits bodyReady functions target
        (valueBinding kindTarget (temporary initial.nextId) :: bindings) indent
        (initial.nextId + 1) rest bodyKind' restEquation bodyFresh bodyDistinct)
/-! ### Cell writes -/

/-- `storeCell` assigns the cell's `sc_c<n>` local after evaluating the value. -/
theorem aRenderIH_storeCell (index : Nat) {value : CoreExpr} (valueIH : ARenderIH value) :
    ARenderIH (.storeCell (.var index) value) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨_, valueKind, resultUnit⟩ := AggregateKinds.storeCell accepted
  have targetUnit : target = .unit := by
    cases target <;> first | rfl | cases resultUnit
  subst targetUnit
  obtain ⟨name, written, result, found, writtenEquation, resultFound, rfl⟩ :=
    AggregateEquations.storeCell_ok equation
  obtain ⟨statements, lines, le, writtenValue, names, simulates⟩ :=
    valueIH admits (AliasesReady.of_sub ready fun uses => by
        simp [AggregateRenderer.usesOpcodeAliases, uses])
      functions .word bindings indent first written valueKind writtenEquation fresh distinct
  refine ⟨statements ++ [.assign name (.name result)], ?_, le, (fun _ same => by cases same),
    ?_, ?_⟩
  · simp only [Stmt.listLines_append, lines, Stmt.listLines, List.append_nil]
  · intro identifier mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at mem
    rcases mem with mem | same | same
    · exact names identifier mem
    · subst same
      exact Or.inl ⟨index, by rw [anameAt_of_getElem? found]; rfl⟩
    · subst same
      exact (writtenValue _ resultFound).uses
  · dsimp only
    intro context environment store scope outer admitted agree distinctCells lengthOk
      functionsOk
    obtain ⟨valueCore, store₁, scope₁, outer₁, added₁, valueEvaluates, valueRepresents,
      valueExec, agree₁, frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
      simulates context environment store scope outer admitted agree distinctCells lengthOk
        functionsOk
    rw [resultFound, Option.bind_some] at valueRepresents
    obtain ⟨_, lookupResult, word, rfl, rfl⟩ := valueRepresents
    obtain ⟨cellCore, inEnvironment, elementType, location, old, rfl, oldRead, _⟩ :=
      agree index _ found
    obtain ⟨cellCore₁, inEnvironment₁, elementType₁, location₁, old₁, sameCell, oldRead₁,
      oldLookup₁⟩ := agree₁ index _ found
    rw [inEnvironment] at inEnvironment₁
    cases inEnvironment₁
    cases sameCell
    have inBounds : location < store₁.length := by
      simp only [Solcore.Core.Store.read?] at oldRead₁
      exact (List.getElem?_eq_some_iff.mp oldRead₁).1
    obtain ⟨store₂, written⟩ :=
      (Solcore.Core.Store.write?_success_iff store₁ location (.word word)).mpr inBounds
    obtain ⟨frames₂, assigned, shapeAssigned, lookups⟩ :=
      Frames.assign_spec (frames := scope₁ :: outer₁) (.word word.val) oldLookup₁
    have shapeCons : frames₂.shape = scope₁.names :: outer₁.shape := by
      rw [shapeAssigned]
      rfl
    obtain ⟨scope₂, outer₂, rfl⟩ : ∃ scope₂ outer₂, frames₂ = scope₂ :: outer₂ := by
      match frames₂, shapeCons with
      | scope₂ :: outer₂, _ => exact ⟨scope₂, outer₂, rfl⟩
      | [], impossible => simp [Frames.shape] at impossible
    simp only [Frames.shape, List.map_cons, List.cons.injEq] at shapeCons
    obtain ⟨scopeNames, outerShape⟩ := shapeCons
    refine ⟨.unit, store₂, scope₂, outer₂, added₁, ?_, rfl, ?_, ?_, ?_, ?_,
      outerShape.trans shape₁, scopeNames.trans names₁, addedTemp₁⟩
    · simp only [Solcore.Core.Wire.Expr.toCore]
      exact .storeCell (.var inEnvironment) oldRead valueEvaluates written
    · rw [Stmt.execList_append, valueExec]
      simp [Stmt.execList, Stmt.exec, Expr.eval, lookupResult, oldLookup₁, Value.sameType,
        assigned]
    · exact agree₁.write distinct distinctCells found inEnvironment written lookups
    · refine frame₁.trans ⟨Nat.le_of_eq
        (Solcore.Core.Store.write?_preserves_length written).symm, fun other _ notCell => ?_⟩
      have otherLocation : other ≠ location := fun same =>
        notCell index (same ▸ ⟨⟨name, found⟩, _, inEnvironment⟩)
      exact Solcore.Core.Store.write?_preserves_other written otherLocation
    · intro other notTemp notCell
      have different : name ≠ other := fun same => notCell index (same ▸ found)
      rw [lookups other, if_neg different, keeps₁ other notTemp notCell]

/-! ### Conditionals -/

/-- An `if` of a value type declares its zero result, then assigns the value
of the selected branch inside the branch block. -/
theorem aifValue_spec {condition yes no : CoreExpr} {target : ATarget}
    {functions : List String} {bindings : List Binding} {indent first : Nat}
    {tested selected fallback : ARendered}
    {conditionValue selectedValue fallbackValue : String}
    (unitTarget : ¬ target = .unit) (fresh : ANamesFresh bindings first)
    (distinct : ANamesDistinct bindings)
    (conditionSpec : ARenderSpec admits condition .bool functions bindings indent first tested)
    (conditionFound : tested.value = some conditionValue)
    (yesSpec : ARenderSpec admits yes target functions bindings (indent + 4) (tested.nextId + 1)
      selected)
    (selectedFound : selected.value = some selectedValue)
    (noSpec : ARenderSpec admits no target functions bindings (indent + 4) selected.nextId
      fallback)
    (fallbackFound : fallback.value = some fallbackValue) :
    ARenderSpec admits (.ifE condition yes no) target functions bindings indent first
      ⟨tested.lines ++
          [indentLine indent ("let " ++ temporary tested.nextId ++ ": " ++
            target.localType.spelling ++ " = " ++ azeroText target ++ ";")] ++
          [indentLine indent ("if (" ++ conditionValue ++ ") {")] ++ selected.lines ++
          [indentLine (indent + 4) (temporary tested.nextId ++ " = " ++ selectedValue ++ ";"),
            indentLine indent "} else {"] ++
          fallback.lines ++
          [indentLine (indent + 4) (temporary tested.nextId ++ " = " ++ fallbackValue ++ ";"),
            indentLine indent "}"],
        some (temporary tested.nextId), fallback.nextId⟩ := by
  have enterNil : ∀ (scope : Scope) (outer : Frames) (environment : Solcore.Core.Environment)
      (store : Solcore.Core.Store), ABindingsAgree (scope :: outer) bindings environment store →
      ABindingsAgree ([] :: scope :: outer) bindings environment store :=
    fun _ _ _ _ agree => agree.enter [] fun _ _ _ => not_mem_names_nil _
  obtain ⟨cStatements, cLines, cLe, cValue, cNames, cSimulates⟩ := conditionSpec
  obtain ⟨yStatements, yLines, yLe, yValue, yNames, ySimulates⟩ := yesSpec
  obtain ⟨nStatements, nLines, nLe, nValue, nNames, nSimulates⟩ := noSpec
  have result : ∀ last, tested.nextId < last → ATempIn first last (temporary tested.nextId) :=
    fun _ lt => aTempIn_temporary cLe lt
  refine ⟨cStatements ++
      [.letDecl (temporary tested.nextId) (ATarget.localType target) (azero target),
        .ifElse (.name conditionValue)
          (yStatements ++ [.assign (temporary tested.nextId) (.name selectedValue)])
          (nStatements ++ [.assign (temporary tested.nextId) (.name fallbackValue)])],
    ?_, by dsimp only; omega, ?_, ?_, ?_⟩
  · simp only [Stmt.listLines_append, cLines, yLines, nLines, Stmt.listLines, Stmt.lines,
      Expr.print, azero_print unitTarget, List.append_nil, List.append_assoc,
      List.cons_append, List.nil_append]
  · intro name same
    cases same
    exact Or.inr ⟨tested.nextId, rfl, cLe, by dsimp only; omega⟩
  · dsimp only
    intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, Expr.identifiers, azero_identifiers, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at mem
    rcases mem with mem | same | (same | mem | same | same) | (mem | same | same)
    · exact (cNames name mem).mono (Nat.le_refl _) (by omega)
    · exact Or.inr (Or.inr (Or.inl (same ▸ result _ (by omega))))
    · subst same
      exact (cValue name conditionFound).uses.mono (Nat.le_refl _) (by omega)
    · exact (yNames name mem).mono (by omega) (by omega)
    · exact Or.inr (Or.inr (Or.inl (same ▸ result _ (by omega))))
    · subst same
      exact (yValue name selectedFound).uses.mono (by omega) (by omega)
    · exact (nNames name mem).mono (by omega) (Nat.le_refl _)
    · exact Or.inr (Or.inr (Or.inl (same ▸ result _ (by omega))))
    · subst same
      exact (nValue name fallbackFound).uses.mono (by omega) (Nat.le_refl _)
  · dsimp only
    intro context environment store scope outer admitted agree distinctCells lengthOk
      functionsOk
    obtain ⟨cCore, store₁, scope₁, outer₁, added₁, cEvaluates, cRepresents, cExec, agree₁,
      frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
      cSimulates context environment store scope outer admitted agree distinctCells lengthOk
        functionsOk
    rw [conditionFound, Option.bind_some] at cRepresents
    obtain ⟨_, cLookup, flag, rfl, rfl⟩ := cRepresents
    have resultTemp := result (tested.nextId + 1) (Nat.lt_succ_self _)
    rw [selectedFound] at ySimulates
    rw [fallbackFound] at nSimulates
    have resultNotBinding : ∀ index found, anameAt bindings index = some found →
        found ≠ temporary tested.nextId := fresh.ne_temp resultTemp
    have agreeDeclared := agree₁.declare (fresh.ne_temp resultTemp) (azeroValue target)
    have declared : Frames.lookup (((temporary tested.nextId, azeroValue target) :: scope₁) ::
        outer₁) (temporary tested.nextId) = some (azeroValue target) := by
      simp [Frames.lookup_declared]
    have conditionSurvives : temporary tested.nextId ≠ conditionValue := by
      intro same
      exact ((cValue conditionValue conditionFound).survives (last := tested.nextId + 1) fresh
        distinct cLe).1 (same ▸ aTempIn_temporary (Nat.le_refl _) (Nat.lt_succ_self _))
    have conditionLookup : Frames.lookup (((temporary tested.nextId, azeroValue target) ::
        scope₁) :: outer₁) conditionValue = some (.bool flag) := by
      rw [Frames.lookup_declared, if_neg conditionSurvives]
      exact cLookup
    have prefixExec : Stmt.execList context (scope :: outer) (cStatements ++
        [.letDecl (temporary tested.nextId) (ATarget.localType target) (azero target)]) =
        some (((temporary tested.nextId, azeroValue target) :: scope₁) :: outer₁) := by
      rw [Stmt.execList_append, cExec]
      simp [Stmt.execList, Stmt.exec, azero_eval, azeroValue_admits, Frames.declare]
    have keepsOutside : ∀ name, ¬ ATempIn first fallback.nextId name →
        (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
        Frames.lookup (((temporary tested.nextId, azeroValue target) :: scope₁) :: outer₁)
          name = Frames.lookup (scope :: outer) name := by
      intro name notTemp notCell
      have different : temporary tested.nextId ≠ name := fun same =>
        notTemp (same ▸ result _ (by omega))
      rw [Frames.lookup_declared, if_neg different,
        keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) (by omega)))
          notCell]
    have scopeNames₁ :
        Scope.names ((temporary tested.nextId, azeroValue target) :: scope₁) =
        (temporary tested.nextId :: added₁) ++ scope.names := by
      show temporary tested.nextId :: scope₁.names = _
      rw [names₁]
      rfl
    have addedOk : ∀ name ∈ temporary tested.nextId :: added₁,
        ATempIn first fallback.nextId name := by
      intro name mem
      rcases List.mem_cons.mp mem with same | mem
      · exact same ▸ result _ (by omega)
      · exact aTempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) (by omega)
    cases flag with
    | true =>
        obtain ⟨branchCore, value, store₂, top, scope₂, outer₂, branchEvaluates,
          branchRepresents, branchExec, agree₂, frame₂, scopeNames, outerShape, lookups⟩ :=
          aarm_value unitTarget ySimulates (fresh.mono (by omega)) admitted
            (enterNil _ _ _ _ agreeDeclared) distinctCells lengthOk functionsOk
            (fun _ _ agree => agree) (fun _ frame => frame) (fun _ notCell => notCell)
            (fun _ _ _ => not_mem_names_nil _)
            (not_aTempIn_of_aTempIn resultTemp (Or.inl (Nat.le_refl _)))
            (not_mem_names_nil _) (fresh.not_cell resultTemp) resultNotBinding declared
        refine ⟨branchCore, store₂, scope₂, outer₂, temporary tested.nextId :: added₁, ?_, ?_,
          ?_, agree₂, frame₁.trans frame₂, ?_, outerShape.trans shape₁,
          scopeNames.trans scopeNames₁, addedOk⟩
        · simp only [Solcore.Core.Wire.Expr.toCore]
          exact .ifTrue cEvaluates branchEvaluates
        · rw [Option.bind_some, lookups _ (not_aTempIn_of_aTempIn resultTemp
            (Or.inl (Nat.le_refl _))) (not_mem_names_nil _) (fresh.not_cell resultTemp),
            if_pos rfl]
          exact ARepresents.of_value branchRepresents
        · rw [List.append_cons, Stmt.execList_append, prefixExec]
          simp [Stmt.execList, Stmt.exec, Expr.eval, conditionLookup, branchExec]
        · intro name notTemp notCell
          have different : temporary tested.nextId ≠ name := fun same =>
            notTemp (same ▸ result _ (by omega))
          rw [lookups name (fun temp => notTemp (aTempIn_mono temp (by omega) (by omega)))
            (not_mem_names_nil _) notCell, if_neg different, keepsOutside name notTemp notCell]
    | false =>
        obtain ⟨branchCore, value, store₂, top, scope₂, outer₂, branchEvaluates,
          branchRepresents, branchExec, agree₂, frame₂, scopeNames, outerShape, lookups⟩ :=
          aarm_value unitTarget nSimulates (fresh.mono (by omega)) admitted
            (enterNil _ _ _ _ agreeDeclared) distinctCells lengthOk functionsOk
            (fun _ _ agree => agree) (fun _ frame => frame) (fun _ notCell => notCell)
            (fun _ _ _ => not_mem_names_nil _)
            (not_aTempIn_of_aTempIn resultTemp (Or.inl (by omega)))
            (not_mem_names_nil _) (fresh.not_cell resultTemp) resultNotBinding declared
        refine ⟨branchCore, store₂, scope₂, outer₂, temporary tested.nextId :: added₁, ?_, ?_,
          ?_, agree₂, frame₁.trans frame₂, ?_, outerShape.trans shape₁,
          scopeNames.trans scopeNames₁, addedOk⟩
        · simp only [Solcore.Core.Wire.Expr.toCore]
          exact .ifFalse cEvaluates branchEvaluates
        · rw [Option.bind_some, lookups _ (not_aTempIn_of_aTempIn resultTemp
            (Or.inl (by omega))) (not_mem_names_nil _) (fresh.not_cell resultTemp),
            if_pos rfl]
          exact ARepresents.of_value branchRepresents
        · rw [List.append_cons, Stmt.execList_append, prefixExec]
          simp [Stmt.execList, Stmt.exec, Expr.eval, conditionLookup, branchExec]
        · intro name notTemp notCell
          have different : temporary tested.nextId ≠ name := fun same =>
            notTemp (same ▸ result _ (by omega))
          rw [lookups name (fun temp => notTemp (aTempIn_mono temp (by omega) (Nat.le_refl _)))
            (not_mem_names_nil _) notCell, if_neg different, keepsOutside name notTemp notCell]

theorem aRenderIH_ifE {condition yes no : CoreExpr} (conditionIH : ARenderIH condition)
    (yesIH : ARenderIH yes) (noIH : ARenderIH no) : ARenderIH (.ifE condition yes no) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨conditionKind, yesKind, noKind, _⟩ := AggregateKinds.ifE accepted
  have conditionReady := AliasesReady.of_sub ready (sub := condition) fun uses => by
    simp [AggregateRenderer.usesOpcodeAliases, uses]
  have yesReady := AliasesReady.of_sub ready (sub := yes) fun uses => by
    simp [AggregateRenderer.usesOpcodeAliases, uses]
  have noReady := AliasesReady.of_sub ready (sub := no) fun uses => by
    simp [AggregateRenderer.usesOpcodeAliases, uses]
  have enterNil : ∀ (scope : Scope) (outer : Frames) (environment : Solcore.Core.Environment)
      (store : Solcore.Core.Store), ABindingsAgree (scope :: outer) bindings environment store →
      ABindingsAgree ([] :: scope :: outer) bindings environment store :=
    fun _ _ _ _ agree => agree.enter [] fun _ _ _ => not_mem_names_nil _
  by_cases unitTarget : target = .unit
  · subst unitTarget
    obtain ⟨tested, conditionValue, selected, fallback, testedEquation, conditionFound,
      selectedEquation, fallbackEquation, rfl⟩ := AggregateEquations.ifE_unit_ok equation
    obtain ⟨cStatements, cLines, cLe, cValue, cNames, cSimulates⟩ :=
      conditionIH admits conditionReady functions .bool bindings indent first tested
        conditionKind testedEquation fresh distinct
    obtain ⟨yStatements, yLines, yLe, _, yNames, ySimulates⟩ :=
      yesIH admits yesReady functions .unit bindings (indent + 4) tested.nextId selected yesKind
        selectedEquation (fresh.mono cLe) distinct
    obtain ⟨nStatements, nLines, nLe, _, nNames, nSimulates⟩ :=
      noIH admits noReady functions .unit bindings (indent + 4) selected.nextId fallback noKind
        fallbackEquation (fresh.mono (by omega)) distinct
    refine ⟨cStatements ++ [.ifElse (.name conditionValue) yStatements nStatements], ?_,
      by dsimp only; omega, (fun _ same => by cases same), ?_, ?_⟩
    · simp only [Stmt.listLines_append, cLines, yLines, nLines, Stmt.listLines, Stmt.lines,
        Expr.print, List.append_nil, List.append_assoc, List.cons_append, List.nil_append]
    · dsimp only
      intro name mem
      simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
        Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false] at mem
      rcases mem with mem | (same | mem) | mem
      · exact (cNames name mem).mono (Nat.le_refl _) (by omega)
      · subst same
        exact (cValue name conditionFound).uses.mono (Nat.le_refl _) (by omega)
      · exact (yNames name mem).mono cLe (by omega)
      · exact (nNames name mem).mono (by omega) (Nat.le_refl _)
    · dsimp only
      intro context environment store scope outer admitted agree distinctCells lengthOk
        functionsOk
      obtain ⟨cCore, store₁, scope₁, outer₁, added₁, cEvaluates, cRepresents, cExec, agree₁,
        frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
        cSimulates context environment store scope outer admitted agree distinctCells lengthOk
          functionsOk
      rw [conditionFound, Option.bind_some] at cRepresents
      obtain ⟨_, cLookup, flag, rfl, rfl⟩ := cRepresents
      have addedOk : ∀ name ∈ added₁, ATempIn first fallback.nextId name :=
        fun name mem => aTempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) (by omega)
      cases flag with
      | true =>
          obtain ⟨store₂, top, scope₂, outer₂, yEvaluates, yExec, agree₂, frame₂, scopeNames,
            outerShape, keeps₂⟩ :=
            aarm_unit ySimulates (fresh.mono cLe) admitted (enterNil _ _ _ _ agree₁)
              distinctCells lengthOk functionsOk (fun _ _ agree => agree) (fun _ frame => frame)
              (fun _ notCell => notCell) (fun _ _ _ => not_mem_names_nil _)
          refine ⟨.unit, store₂, scope₂, outer₂, added₁, ?_, rfl, ?_, agree₂, frame₁.trans frame₂,
            ?_, outerShape.trans shape₁, scopeNames.trans names₁, addedOk⟩
          · simp only [Solcore.Core.Wire.Expr.toCore]
            exact .ifTrue cEvaluates yEvaluates
          · rw [Stmt.execList_append, cExec]
            simp [Stmt.execList, Stmt.exec, Expr.eval, cLookup, yExec]
          · intro name notTemp notCell
            rw [keeps₂ name (fun temp => notTemp (aTempIn_mono temp cLe (by omega)))
                (not_mem_names_nil _) notCell,
              keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) (by omega)))
                notCell]
      | false =>
          obtain ⟨store₂, top, scope₂, outer₂, nEvaluates, nExec, agree₂, frame₂, scopeNames,
            outerShape, keeps₂⟩ :=
            aarm_unit nSimulates (fresh.mono (by omega)) admitted (enterNil _ _ _ _ agree₁)
              distinctCells lengthOk functionsOk (fun _ _ agree => agree) (fun _ frame => frame)
              (fun _ notCell => notCell) (fun _ _ _ => not_mem_names_nil _)
          refine ⟨.unit, store₂, scope₂, outer₂, added₁, ?_, rfl, ?_, agree₂, frame₁.trans frame₂,
            ?_, outerShape.trans shape₁, scopeNames.trans names₁, addedOk⟩
          · simp only [Solcore.Core.Wire.Expr.toCore]
            exact .ifFalse cEvaluates nEvaluates
          · rw [Stmt.execList_append, cExec]
            simp [Stmt.execList, Stmt.exec, Expr.eval, cLookup, nExec]
          · intro name notTemp notCell
            rw [keeps₂ name (fun temp => notTemp (aTempIn_mono temp (by omega) (Nat.le_refl _)))
                (not_mem_names_nil _) notCell,
              keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) (by omega)))
                notCell]
  · obtain ⟨tested, conditionValue, selected, selectedValue, fallback, fallbackValue,
      testedEquation, conditionFound, selectedEquation, selectedFound, fallbackEquation,
      fallbackFound, rfl⟩ := AggregateEquations.ifE_value_ok unitTarget equation
    have conditionSpec := conditionIH admits conditionReady functions .bool bindings indent
      first tested conditionKind testedEquation fresh distinct
    have yesSpec := yesIH admits yesReady functions target bindings (indent + 4)
      (tested.nextId + 1) selected yesKind selectedEquation
      (fresh.mono (by have := conditionSpec.le; omega)) distinct
    have noSpec := noIH admits noReady functions target bindings (indent + 4) selected.nextId
      fallback noKind fallbackEquation
      (fresh.mono (by have := conditionSpec.le; have := yesSpec.le; omega)) distinct
    exact aifValue_spec unitTarget fresh distinct conditionSpec conditionFound yesSpec
      selectedFound noSpec fallbackFound
/-! ### Sum cases -/

/-- A case body sees one more binding: its payload, named by a fresh pattern
temporary. -/
theorem payload_fresh {bindings : List Binding} {first payload : Nat}
    (fresh : ANamesFresh bindings first) (le : first ≤ payload) :
    ANamesFresh (.word (payloadTemp payload) :: bindings) (payload + 1) :=
  fresh.cons (by omega) fun name same => by
    cases same
    exact payloadTemp_fresh _

theorem payload_distinct {bindings : List Binding} {first payload : Nat}
    (fresh : ANamesFresh bindings first) (distinct : ANamesDistinct bindings)
    (le : first ≤ payload) : ANamesDistinct (.word (payloadTemp payload) :: bindings) :=
  distinct.cons fresh fun name same => by
    cases same
    exact ⟨payload, Or.inr (Or.inr rfl), le⟩

theorem payload_absent {bindings : List Binding} {first payload : Nat}
    (fresh : ANamesFresh bindings first) (le : first ≤ payload) :
    ∀ index found, anameAt bindings index = some found → found ≠ payloadTemp payload := by
  intro index found named same
  have := fresh index found named payload (Or.inr (Or.inr same))
  omega

theorem payload_outside {bindings : List Binding} {first payload : Nat}
    (fresh : ANamesFresh bindings first) (le : first ≤ payload) (word : Value) :
    ∀ index name, anameAt bindings index = some name →
      name ∉ Scope.names [(payloadTemp payload, word)] := by
  intro index name named mem
  simp only [Scope.names, List.map_cons, List.map_nil, List.mem_singleton] at mem
  exact payload_absent fresh le index name named mem

theorem payload_cells {bindings : List Binding} (payload name : String) :
    (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
      ∀ index : Nat, (Binding.word payload :: bindings)[index]? ≠ some (Binding.cellWord name) := by
  intro notCell index
  cases index with
  | zero => simp
  | succ index => simpa using notCell index

theorem payload_kinds (payload : String) (bindings : List Binding) :
    (Binding.word payload :: bindings).map Binding.kind = .word :: bindings.map Binding.kind :=
  rfl

/-- A sum `case` of a value type declares its zero result and matches the
scrutinee once; the selected case binds the payload under a fresh pattern name
and assigns its value to the result. -/
theorem acaseValue_spec {scrutinee yes no : CoreExpr} {target : ATarget}
    {functions : List String} {bindings : List Binding} {indent first : Nat}
    {tested selected fallback : ARendered} {value selectedValue fallbackValue : String}
    (unitTarget : ¬ target = .unit) (fresh : ANamesFresh bindings first)
    (distinct : ANamesDistinct bindings)
    (scrutineeSpec : ARenderSpec admits scrutinee .wordSum functions bindings indent first
      tested)
    (valueFound : tested.value = some value)
    (yesSpec : ARenderSpec admits yes target functions
      (.word (payloadTemp (tested.nextId + 1)) :: bindings) (indent + 8) (tested.nextId + 2)
      selected)
    (selectedFound : selected.value = some selectedValue)
    (noSpec : ARenderSpec admits no target functions
      (.word (payloadTemp selected.nextId) :: bindings) (indent + 8) (selected.nextId + 1)
      fallback)
    (fallbackFound : fallback.value = some fallbackValue) :
    ARenderSpec admits (.caseE scrutinee yes no) target functions bindings indent first
      ⟨tested.lines ++
          [indentLine indent ("let " ++ temporary tested.nextId ++ ": " ++
            target.localType.spelling ++ " = " ++ azeroText target ++ ";")] ++
          [indentLine indent ("match (" ++ value ++ ") {"),
            indentLine (indent + 4) ("case inl(" ++ payloadTemp (tested.nextId + 1) ++ ") {")] ++
          (selected.lines ++
            [indentLine (indent + 8) (temporary tested.nextId ++ " = " ++ selectedValue ++ ";")]) ++
          [indentLine (indent + 4) "}",
            indentLine (indent + 4)
              ("case inr(" ++ payloadTemp selected.nextId ++ ") {")] ++
          (fallback.lines ++
            [indentLine (indent + 8) (temporary tested.nextId ++ " = " ++ fallbackValue ++ ";")]) ++
          [indentLine (indent + 4) "}", indentLine indent "}"],
        some (temporary tested.nextId), fallback.nextId⟩ := by
  obtain ⟨sStatements, sLines, sLe, sValue, sNames, sSimulates⟩ := scrutineeSpec
  obtain ⟨yStatements, yLines, yLe, yValue, yNames, ySimulates⟩ := yesSpec
  obtain ⟨nStatements, nLines, nLe, nValue, nNames, nSimulates⟩ := noSpec
  have result : ∀ last, tested.nextId < last → ATempIn first last (temporary tested.nextId) :=
    fun _ lt => aTempIn_temporary sLe lt
  have leftTemp : ATempIn first fallback.nextId (payloadTemp (tested.nextId + 1)) :=
    aTempIn_payloadTemp (by omega) (by omega)
  have rightTemp : ATempIn first fallback.nextId (payloadTemp selected.nextId) :=
    aTempIn_payloadTemp (by omega) (by omega)
  refine ⟨sStatements ++
      [.letDecl (temporary tested.nextId) (ATarget.localType target) (azero target),
        .matchSum (.name value) (payloadTemp (tested.nextId + 1))
          (yStatements ++ [.assign (temporary tested.nextId) (.name selectedValue)])
          (payloadTemp selected.nextId)
          (nStatements ++ [.assign (temporary tested.nextId) (.name fallbackValue)])],
    ?_, by dsimp only; omega, ?_, ?_, ?_⟩
  · simp only [Stmt.listLines_append, sLines, yLines, nLines, Stmt.listLines, Stmt.lines,
      Expr.print, azero_print unitTarget, List.append_nil, List.append_assoc,
      List.cons_append, List.nil_append]
  · intro name same
    cases same
    exact Or.inr ⟨tested.nextId, rfl, sLe, by dsimp only; omega⟩
  · dsimp only
    intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, Expr.identifiers, azero_identifiers, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at mem
    rcases mem with mem | same | ((same | same | mem | same | same) | same | mem | same | same)
    · exact (sNames name mem).mono (Nat.le_refl _) (by omega)
    · exact Or.inr (Or.inr (Or.inl (same ▸ result _ (by omega))))
    · subst same
      exact (sValue name valueFound).uses.mono (Nat.le_refl _) (by omega)
    · exact Or.inr (Or.inr (Or.inl (same ▸ leftTemp)))
    · exact ((yNames name mem).of_cons (fun found same => by
        cases same
        exact aTempIn_payloadTemp (by omega) (by omega)) (by omega)).mono (Nat.le_refl _)
          (by omega)
    · exact Or.inr (Or.inr (Or.inl (same ▸ result _ (by omega))))
    · subst same
      exact ((yValue name selectedFound).uses.of_cons
        (fun found same => by
          cases same
          exact aTempIn_payloadTemp (by omega) (by omega)) (by omega)).mono (Nat.le_refl _)
          (by omega)
    · exact Or.inr (Or.inr (Or.inl (same ▸ rightTemp)))
    · exact ((nNames name mem).of_cons (fun found same => by cases same; exact rightTemp)
        (by omega)).mono (Nat.le_refl _) (Nat.le_refl _)
    · exact Or.inr (Or.inr (Or.inl (same ▸ result _ (by omega))))
    · subst same
      exact ((nValue name fallbackFound).uses.of_cons
        (fun found same => by cases same; exact rightTemp) (by omega)).mono (Nat.le_refl _)
          (Nat.le_refl _)
  · dsimp only
    intro context environment store scope outer admitted agree distinctCells lengthOk
      functionsOk
    obtain ⟨sCore, store₁, scope₁, outer₁, added₁, sEvaluates, sRepresents, sExec, agree₁,
      frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
      sSimulates context environment store scope outer admitted agree distinctCells lengthOk
        functionsOk
    rw [valueFound, Option.bind_some] at sRepresents
    obtain ⟨sumSource, sLookup, sumValue⟩ := sRepresents
    have resultTemp := result (tested.nextId + 1) (Nat.lt_succ_self _)
    rw [selectedFound] at ySimulates
    rw [fallbackFound] at nSimulates
    have resultNotBinding : ∀ index found, anameAt bindings index = some found →
        found ≠ temporary tested.nextId := fresh.ne_temp resultTemp
    have agreeDeclared := agree₁.declare (fresh.ne_temp resultTemp) (azeroValue target)
    have declared : Frames.lookup (((temporary tested.nextId, azeroValue target) :: scope₁) ::
        outer₁) (temporary tested.nextId) = some (azeroValue target) := by
      simp [Frames.lookup_declared]
    have scrutineeSurvives : temporary tested.nextId ≠ value := by
      intro same
      exact ((sValue value valueFound).survives (last := tested.nextId + 1) fresh distinct
        sLe).1 (same ▸ aTempIn_temporary (Nat.le_refl _) (Nat.lt_succ_self _))
    have scrutineeLookup : Frames.lookup (((temporary tested.nextId, azeroValue target) ::
        scope₁) :: outer₁) value = some sumSource := by
      rw [Frames.lookup_declared, if_neg scrutineeSurvives]
      exact sLookup
    have prefixExec : Stmt.execList context (scope :: outer) (sStatements ++
        [.letDecl (temporary tested.nextId) (ATarget.localType target) (azero target)]) =
        some (((temporary tested.nextId, azeroValue target) :: scope₁) :: outer₁) := by
      rw [Stmt.execList_append, sExec]
      simp [Stmt.execList, Stmt.exec, azero_eval, azeroValue_admits, Frames.declare]
    have keepsOutside : ∀ name, ¬ ATempIn first fallback.nextId name →
        (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
        Frames.lookup (((temporary tested.nextId, azeroValue target) :: scope₁) :: outer₁)
          name = Frames.lookup (scope :: outer) name := by
      intro name notTemp notCell
      have different : temporary tested.nextId ≠ name := fun same =>
        notTemp (same ▸ result _ (by omega))
      rw [Frames.lookup_declared, if_neg different,
        keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) (by omega)))
          notCell]
    have scopeNames₁ :
        Scope.names ((temporary tested.nextId, azeroValue target) :: scope₁) =
        (temporary tested.nextId :: added₁) ++ scope.names := by
      show temporary tested.nextId :: scope₁.names = _
      rw [names₁]
      rfl
    have addedOk : ∀ name ∈ temporary tested.nextId :: added₁,
        ATempIn first fallback.nextId name := by
      intro name mem
      rcases List.mem_cons.mp mem with same | mem
      · exact same ▸ result _ (by omega)
      · exact aTempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) (by omega)
    have resultNotPayload : ∀ payload : Nat, ∀ word : Value,
        temporary tested.nextId ∉ Scope.names [(payloadTemp payload, word)] := by
      intro payload word mem
      simp only [Scope.names, List.map_cons, List.map_nil, List.mem_singleton] at mem
      exact payloadTemp_ne_temporary _ _ mem.symm
    rcases sumValue with ⟨type, payload, rfl, rfl⟩ | ⟨type, payload, rfl, rfl⟩
    · obtain ⟨branchCore, branchValue, store₂, top, scope₂, outer₂, branchEvaluates,
        branchRepresents, branchExec, agree₂, frame₂, scopeNames, outerShape, lookups⟩ :=
        aarm_value (bindings := bindings) (environment := environment) unitTarget ySimulates
          (fresh.mono (by omega)) admitted
          (agreeDeclared.payload (payload_absent fresh (by omega)) payload)
          (distinctCells.cons_value fun _ same => by cases same) (by simp; omega)
          (by simpa using functionsOk) (fun _ _ agree => agree.tail)
          (fun _ frame => frame.of_cons fun _ same => by cases same)
          (payload_cells _) (payload_outside fresh (by omega) _)
          (not_aTempIn_of_aTempIn resultTemp (Or.inl (by omega)))
          (resultNotPayload _ _) (fresh.not_cell resultTemp) resultNotBinding declared
      refine ⟨branchCore, store₂, scope₂, outer₂, temporary tested.nextId :: added₁, ?_, ?_,
        ?_, agree₂, frame₁.trans frame₂, ?_, outerShape.trans shape₁,
        scopeNames.trans scopeNames₁, addedOk⟩
      · simp only [Solcore.Core.Wire.Expr.toCore]
        exact .caseLeft sEvaluates branchEvaluates
      · rw [Option.bind_some, lookups _ (not_aTempIn_of_aTempIn resultTemp
          (Or.inl (by omega))) (resultNotPayload _ _) (fresh.not_cell resultTemp), if_pos rfl]
        exact ARepresents.of_value branchRepresents
      · rw [List.append_cons, Stmt.execList_append, prefixExec]
        simp [Stmt.execList, Stmt.exec, Expr.eval, scrutineeLookup, branchExec]
      · intro name notTemp notCell
        have different : temporary tested.nextId ≠ name := fun same =>
          notTemp (same ▸ result _ (by omega))
        rw [lookups name (fun temp => notTemp (aTempIn_mono temp (by omega) (by omega)))
            (fun mem => by
              simp only [Scope.names, List.map_cons, List.map_nil, List.mem_singleton] at mem
              exact notTemp (mem ▸ leftTemp)) notCell,
          if_neg different, keepsOutside name notTemp notCell]
    · obtain ⟨branchCore, branchValue, store₂, top, scope₂, outer₂, branchEvaluates,
        branchRepresents, branchExec, agree₂, frame₂, scopeNames, outerShape, lookups⟩ :=
        aarm_value (bindings := bindings) (environment := environment) unitTarget nSimulates
          (fresh.mono (by omega)) admitted
          (agreeDeclared.payload (payload_absent fresh (by omega)) payload)
          (distinctCells.cons_value fun _ same => by cases same) (by simp; omega)
          (by simpa using functionsOk) (fun _ _ agree => agree.tail)
          (fun _ frame => frame.of_cons fun _ same => by cases same)
          (payload_cells _) (payload_outside fresh (by omega) _)
          (not_aTempIn_of_aTempIn resultTemp (Or.inl (by omega)))
          (resultNotPayload _ _) (fresh.not_cell resultTemp) resultNotBinding declared
      refine ⟨branchCore, store₂, scope₂, outer₂, temporary tested.nextId :: added₁, ?_, ?_,
        ?_, agree₂, frame₁.trans frame₂, ?_, outerShape.trans shape₁,
        scopeNames.trans scopeNames₁, addedOk⟩
      · simp only [Solcore.Core.Wire.Expr.toCore]
        exact .caseRight sEvaluates branchEvaluates
      · rw [Option.bind_some, lookups _ (not_aTempIn_of_aTempIn resultTemp
          (Or.inl (by omega))) (resultNotPayload _ _) (fresh.not_cell resultTemp), if_pos rfl]
        exact ARepresents.of_value branchRepresents
      · rw [List.append_cons, Stmt.execList_append, prefixExec]
        simp [Stmt.execList, Stmt.exec, Expr.eval, scrutineeLookup, branchExec]
      · intro name notTemp notCell
        have different : temporary tested.nextId ≠ name := fun same =>
          notTemp (same ▸ result _ (by omega))
        rw [lookups name (fun temp => notTemp (aTempIn_mono temp (by omega) (Nat.le_refl _)))
            (fun mem => by
              simp only [Scope.names, List.map_cons, List.map_nil, List.mem_singleton] at mem
              exact notTemp (mem ▸ rightTemp)) notCell,
          if_neg different, keepsOutside name notTemp notCell]

theorem aRenderIH_caseE {scrutinee yes no : CoreExpr} (scrutineeIH : ARenderIH scrutinee)
    (yesIH : ARenderIH yes) (noIH : ARenderIH no) : ARenderIH (.caseE scrutinee yes no) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨scrutineeKind, yesKind, noKind, _⟩ := AggregateKinds.caseE accepted
  have scrutineeReady := AliasesReady.of_sub ready (sub := scrutinee) fun uses => by
    simp [AggregateRenderer.usesOpcodeAliases, uses]
  have yesReady := AliasesReady.of_sub ready (sub := yes) fun uses => by
    simp [AggregateRenderer.usesOpcodeAliases, uses]
  have noReady := AliasesReady.of_sub ready (sub := no) fun uses => by
    simp [AggregateRenderer.usesOpcodeAliases, uses]
  by_cases unitTarget : target = .unit
  · subst unitTarget
    obtain ⟨tested, value, selected, fallback, testedEquation, valueFound, selectedEquation,
      fallbackEquation, rfl⟩ := AggregateEquations.caseE_unit_ok equation
    obtain ⟨sStatements, sLines, sLe, sValue, sNames, sSimulates⟩ :=
      scrutineeIH admits scrutineeReady functions .wordSum bindings indent first tested
        scrutineeKind testedEquation fresh distinct
    obtain ⟨yStatements, yLines, yLe, _, yNames, ySimulates⟩ :=
      yesIH admits yesReady functions .unit (.word (payloadTemp tested.nextId) :: bindings)
        (indent + 8) (tested.nextId + 1) selected (by rw [payload_kinds]; exact yesKind)
        selectedEquation (payload_fresh fresh sLe) (payload_distinct fresh distinct sLe)
    obtain ⟨nStatements, nLines, nLe, _, nNames, nSimulates⟩ :=
      noIH admits noReady functions .unit (.word (payloadTemp selected.nextId) :: bindings)
        (indent + 8) (selected.nextId + 1) fallback (by rw [payload_kinds]; exact noKind)
        fallbackEquation (payload_fresh fresh (by omega))
        (payload_distinct fresh distinct (by omega))
    refine ⟨sStatements ++ [.matchSum (.name value) (payloadTemp tested.nextId) yStatements
        (payloadTemp selected.nextId) nStatements], ?_,
      by dsimp only; omega, (fun _ same => by cases same), ?_, ?_⟩
    · simp only [Stmt.listLines_append, sLines, yLines, nLines, Stmt.listLines, Stmt.lines,
        Expr.print, List.append_nil, List.append_assoc, List.cons_append, List.nil_append]
    · dsimp only
      intro name mem
      simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
        Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false] at mem
      have leftTemp : ATempIn first fallback.nextId (payloadTemp tested.nextId) :=
        aTempIn_payloadTemp sLe (by omega)
      have rightTemp : ATempIn first fallback.nextId (payloadTemp selected.nextId) :=
        aTempIn_payloadTemp (by omega) (by omega)
      rcases mem with mem | ((same | same | mem) | same | mem)
      · exact (sNames name mem).mono (Nat.le_refl _) (by omega)
      · subst same
        exact (sValue name valueFound).uses.mono (Nat.le_refl _) (by omega)
      · exact Or.inr (Or.inr (Or.inl (same ▸ leftTemp)))
      · exact ((yNames name mem).of_cons (fun found same => by
          cases same
          exact aTempIn_payloadTemp (by omega) (by omega)) (by omega)).mono (Nat.le_refl _)
            (by omega)
      · exact Or.inr (Or.inr (Or.inl (same ▸ rightTemp)))
      · exact ((nNames name mem).of_cons (fun found same => by cases same; exact rightTemp)
          (by omega)).mono (Nat.le_refl _) (Nat.le_refl _)
    · dsimp only
      intro context environment store scope outer admitted agree distinctCells lengthOk
        functionsOk
      obtain ⟨sCore, store₁, scope₁, outer₁, added₁, sEvaluates, sRepresents, sExec, agree₁,
        frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
        sSimulates context environment store scope outer admitted agree distinctCells lengthOk
          functionsOk
      rw [valueFound, Option.bind_some] at sRepresents
      obtain ⟨_, sLookup, sumValue⟩ := sRepresents
      have addedOk : ∀ name ∈ added₁, ATempIn first fallback.nextId name :=
        fun name mem => aTempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) (by omega)
      rcases sumValue with ⟨type, payload, rfl, rfl⟩ | ⟨type, payload, rfl, rfl⟩
      · obtain ⟨store₂, top, scope₂, outer₂, yEvaluates, yExec, agree₂, frame₂, scopeNames,
          outerShape, keeps₂⟩ :=
          aarm_unit (bindings := bindings) (environment := environment) ySimulates
            (fresh.mono (by omega)) admitted
            (agree₁.payload (payload_absent fresh sLe) payload)
            (distinctCells.cons_value fun _ same => by cases same) (by simp; omega)
            (by simpa using functionsOk) (fun _ _ agree => agree.tail)
            (fun _ frame => frame.of_cons fun _ same => by cases same)
            (payload_cells _) (payload_outside fresh sLe _)
        refine ⟨.unit, store₂, scope₂, outer₂, added₁, ?_, rfl, ?_, agree₂, frame₁.trans frame₂,
          ?_, outerShape.trans shape₁, scopeNames.trans names₁, addedOk⟩
        · simp only [Solcore.Core.Wire.Expr.toCore]
          exact .caseLeft sEvaluates yEvaluates
        · rw [Stmt.execList_append, sExec]
          simp [Stmt.execList, Stmt.exec, Expr.eval, sLookup, yExec]
        · intro name notTemp notCell
          rw [keeps₂ name (fun temp => notTemp (aTempIn_mono temp (by omega) (by omega)))
              (fun mem => by
                simp only [Scope.names, List.map_cons, List.map_nil, List.mem_singleton] at mem
                exact notTemp (mem ▸ aTempIn_payloadTemp sLe (by omega))) notCell,
            keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) (by omega)))
              notCell]
      · obtain ⟨store₂, top, scope₂, outer₂, nEvaluates, nExec, agree₂, frame₂, scopeNames,
          outerShape, keeps₂⟩ :=
          aarm_unit (bindings := bindings) (environment := environment) nSimulates
            (fresh.mono (by omega)) admitted
            (agree₁.payload (payload_absent fresh (by omega)) payload)
            (distinctCells.cons_value fun _ same => by cases same) (by simp; omega)
            (by simpa using functionsOk) (fun _ _ agree => agree.tail)
            (fun _ frame => frame.of_cons fun _ same => by cases same)
            (payload_cells _) (payload_outside fresh (by omega) _)
        refine ⟨.unit, store₂, scope₂, outer₂, added₁, ?_, rfl, ?_, agree₂, frame₁.trans frame₂,
          ?_, outerShape.trans shape₁, scopeNames.trans names₁, addedOk⟩
        · simp only [Solcore.Core.Wire.Expr.toCore]
          exact .caseRight sEvaluates nEvaluates
        · rw [Stmt.execList_append, sExec]
          simp [Stmt.execList, Stmt.exec, Expr.eval, sLookup, nExec]
        · intro name notTemp notCell
          rw [keeps₂ name (fun temp => notTemp (aTempIn_mono temp (by omega) (Nat.le_refl _)))
              (fun mem => by
                simp only [Scope.names, List.map_cons, List.map_nil, List.mem_singleton] at mem
                exact notTemp (mem ▸ aTempIn_payloadTemp (by omega) (by omega))) notCell,
            keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) (by omega)))
              notCell]
  · obtain ⟨tested, value, selected, selectedValue, fallback, fallbackValue, testedEquation,
      valueFound, selectedEquation, selectedFound, fallbackEquation, fallbackFound, rfl⟩ :=
      AggregateEquations.caseE_value_ok unitTarget equation
    have scrutineeSpec := scrutineeIH admits scrutineeReady functions .wordSum bindings indent
      first tested scrutineeKind testedEquation fresh distinct
    have sLe := scrutineeSpec.le
    have yesSpec := yesIH admits yesReady functions target
      (.word (payloadTemp (tested.nextId + 1)) :: bindings) (indent + 8) (tested.nextId + 2)
      selected (by rw [payload_kinds]; exact yesKind) selectedEquation
      (payload_fresh fresh (by omega)) (payload_distinct fresh distinct (by omega))
    have yLe := yesSpec.le
    have noSpec := noIH admits noReady functions target
      (.word (payloadTemp selected.nextId) :: bindings) (indent + 8) (selected.nextId + 1)
      fallback (by rw [payload_kinds]; exact noKind) fallbackEquation
      (payload_fresh fresh (by omega)) (payload_distinct fresh distinct (by omega))
    exact acaseValue_spec unitTarget fresh distinct scrutineeSpec valueFound yesSpec
      selectedFound noSpec fallbackFound
/-! ### Projections -/

/-- A projection declares its zero result, matches the pair once, and assigns
the picked component inside the case scope. -/
theorem projection_exec (context : Context) (scope : Scope) (outer : Frames) (next : Nat)
    (value : String) (left right : Nat) (pickFirst : Bool)
    (lookup : Frames.lookup (scope :: outer) value = some (.pair left right))
    (distinct : temporary next ≠ value) :
    Stmt.execList context (scope :: outer)
        (projectionStmts next value (if pickFirst then next + 1 else next + 2)) =
      some (((temporary next, .word (if pickFirst then left else right)) :: scope) :: outer) := by
  have lookup' : Frames.lookup (((temporary next, .word 0) :: scope) :: outer) value =
      some (.pair left right) := by
    rw [Frames.lookup_declared, if_neg distinct]
    exact lookup
  have firstNe : payloadTemp (next + 2) ≠ payloadTemp (next + 1) := fun same => by
    have := payloadTemp_injective same
    omega
  have zero : 0 < Evm.modulus := Nat.two_pow_pos 256
  have resultLookup : ∀ word : Value, Frames.lookup ([(payloadTemp (next + 2), .word right),
      (payloadTemp (next + 1), .word left)] :: ((temporary next, word) :: scope) :: outer)
      (temporary next) = some word := by
    intro word
    simp [Frames.lookup, Scope.get?, payloadTemp_ne_temporary]
  have firstLookup : ∀ word : Value, Frames.lookup ([(payloadTemp (next + 2), .word right),
      (payloadTemp (next + 1), .word left)] :: ((temporary next, word) :: scope) :: outer)
      (payloadTemp (next + 1)) = some (.word left) := by
    intro word
    simp [Frames.lookup, Scope.get?, firstNe]
  have secondLookup : ∀ word : Value, Frames.lookup ([(payloadTemp (next + 2), .word right),
      (payloadTemp (next + 1), .word left)] :: ((temporary next, word) :: scope) :: outer)
      (payloadTemp (next + 2)) = some (.word right) := by
    intro word
    simp [Frames.lookup, Scope.get?]
  have assigned : ∀ old new : Value, Frames.assign ([(payloadTemp (next + 2), .word right),
      (payloadTemp (next + 1), .word left)] :: ((temporary next, old) :: scope) :: outer)
      (temporary next) new = some ([(payloadTemp (next + 2), .word right),
        (payloadTemp (next + 1), .word left)] :: ((temporary next, new) :: scope) :: outer) := by
    intro old new
    simp [Frames.assign, Scope.set?, payloadTemp_ne_temporary]
  cases pickFirst <;>
    simp [projectionStmts, Stmt.execList, Stmt.exec, Expr.eval, zero, LocalType.admits,
      Frames.declare, lookup', resultLookup, firstLookup, secondLookup, assigned, Value.sameType]

theorem aprojection_spec {expression operand : CoreExpr} {functions : List String}
    {bindings : List Binding} {indent first : Nat} {operandRendered : ARendered}
    {value : String} (pickFirst : Bool)
    (fresh : ANamesFresh bindings first) (distinct : ANamesDistinct bindings)
    (spec : ARenderSpec admits operand .wordPair functions bindings indent first operandRendered)
    (named : operandRendered.value = some value)
    (core : ∀ (environment : Solcore.Core.Environment) (store store₁ : Solcore.Core.Store)
      (left right : Solcore.Core.Word),
      Solcore.Core.Evaluates environment store operand.toCore
        (.pair (.word left) (.word right)) store₁ →
      Solcore.Core.Evaluates environment store expression.toCore
        (.word (if pickFirst then left else right)) store₁) :
    ARenderSpec admits expression .word functions bindings indent first
      ⟨operandRendered.lines ++ Stmt.listLines indent (projectionStmts operandRendered.nextId value
          (if pickFirst then operandRendered.nextId + 1 else operandRendered.nextId + 2)),
        some (temporary operandRendered.nextId), operandRendered.nextId + 3⟩ := by
  obtain ⟨statements, lines, le, valueName, uses, simulates⟩ := spec
  unfold ARenderSpec
  dsimp only
  have resultTemp : ATempIn first (operandRendered.nextId + 3)
      (temporary operandRendered.nextId) := aTempIn_temporary le (by omega)
  refine ⟨statements ++ projectionStmts operandRendered.nextId value
      (if pickFirst then operandRendered.nextId + 1 else operandRendered.nextId + 2), ?_,
    by omega, ?_, ?_, ?_⟩
  · simp only [Stmt.listLines_append, lines]
  · intro name same
    cases same
    exact Or.inr ⟨operandRendered.nextId, rfl, le, by omega⟩
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append] at mem
    rcases mem with mem | mem
    · exact (uses name mem).mono (Nat.le_refl _) (by omega)
    · simp only [projectionStmts, Stmt.listIdentifiers, Stmt.identifiers, Expr.identifiers,
        List.append_nil, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at mem
      rcases mem with same | same | same | same | same | same
      · exact Or.inr (Or.inr (Or.inl (same ▸ resultTemp)))
      · subst same
        exact (valueName name named).uses.mono (Nat.le_refl _) (by omega)
      · exact Or.inr (Or.inr (Or.inl (same ▸ aTempIn_payloadTemp (by omega) (by omega))))
      · exact Or.inr (Or.inr (Or.inl (same ▸ aTempIn_payloadTemp (by omega) (by omega))))
      · exact Or.inr (Or.inr (Or.inl (same ▸ resultTemp)))
      · refine Or.inr (Or.inr (Or.inl (same ▸ ?_)))
        cases pickFirst <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          exact aTempIn_payloadTemp (by omega) (by omega)
  · refine aresult_simulates fresh (fun context environment store scope outer admitted agree
      distinctCells lengthOk functionsOk => ?_) le (by omega)
    obtain ⟨operandCore, store₁, scope₁, outer₁, added₁, evaluates, represents, exec, agree₁,
      frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
      simulates context environment store scope outer admitted agree distinctCells lengthOk
        functionsOk
    rw [named, Option.bind_some] at represents
    obtain ⟨_, lookup, left, right, rfl, rfl⟩ := represents
    have distinctName : temporary operandRendered.nextId ≠ value := by
      intro same
      exact ((valueName value named).survives (last := operandRendered.nextId + 1) fresh
        distinct le).1 (same ▸ aTempIn_temporary (Nat.le_refl _) (Nat.lt_succ_self _))
    have tail := projection_exec context scope₁ outer₁ operandRendered.nextId value left.val
      right.val pickFirst lookup distinctName
    refine ⟨.word (if pickFirst then left else right),
      .word (if pickFirst then left.val else right.val), store₁, scope₁, outer₁, added₁,
      core _ _ _ _ _ evaluates, ?_, exec, tail, agree₁, frame₁, keeps₁, shape₁, names₁,
      addedTemp₁⟩
    cases pickFirst
    · exact ⟨right, rfl, rfl⟩
    · exact ⟨left, rfl, rfl⟩

theorem aRenderIH_first {operand : CoreExpr} (operandIH : ARenderIH operand) :
    ARenderIH (.first operand) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨operandKind, resultWord⟩ := AggregateKinds.first accepted
  have targetWord : target = .word := by
    cases target <;> first | rfl | cases resultWord
  subst targetWord
  obtain ⟨operandRendered, value, operandEquation, named, rfl⟩ :=
    AggregateEquations.first_ok equation
  have spec := operandIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .wordPair bindings indent first operandRendered operandKind operandEquation fresh
    distinct
  exact aprojection_spec true fresh distinct spec named fun _ _ _ _ _ evaluates => by
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .first evaluates

theorem aRenderIH_second {operand : CoreExpr} (operandIH : ARenderIH operand) :
    ARenderIH (.second operand) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨operandKind, resultWord⟩ := AggregateKinds.second accepted
  have targetWord : target = .word := by
    cases target <;> first | rfl | cases resultWord
  subst targetWord
  obtain ⟨operandRendered, value, operandEquation, named, rfl⟩ :=
    AggregateEquations.second_ok equation
  have spec := operandIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .wordPair bindings indent first operandRendered operandKind operandEquation fresh
    distinct
  exact aprojection_spec false fresh distinct spec named fun _ _ _ _ _ evaluates => by
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .second evaluates

end

/-! ### The structural induction -/

/-- An expression the profile never accepts at a value or Unit target. -/
theorem aRenderIH_rejected (expression : CoreExpr)
    (rejected : ∀ locals prior, initializerKind? locals prior expression = none ∨
      initializerKind? locals prior expression = some .cellWord) :
    ARenderIH expression := by
  intro _ _ functions target bindings _ _ _ accepted
  rcases rejected (bindings.map Binding.kind) functions.length with none | cell
  · rw [none] at accepted
    cases accepted
  · rw [cell] at accepted
    cases target <;> cases accepted

theorem aRenderIH_let {initializer body : CoreExpr} (initializerIH : ARenderIH initializer)
    (cellIH : ∀ inner, initializer = .newCell .word inner → ARenderIH inner)
    (bodyIH : ARenderIH body) : ARenderIH (.letE initializer body) := by
  by_cases cell : ∃ inner, initializer = .newCell .word inner
  · obtain ⟨inner, rfl⟩ := cell
    exact aRenderIH_newCellLet (cellIH inner rfl) bodyIH
  · exact aRenderIH_letE (fun inner same => cell ⟨inner, same⟩) initializerIH bodyIH

theorem aRenderIH_unary {op : Solcore.Core.Wire.UnaryOp} {operand : CoreExpr}
    (operandIH : ARenderIH operand) : ARenderIH (.unary op operand) := by
  cases selected : sourceUnary? op with
  | some _ => exact aRenderIH_unarySource selected operandIH
  | none =>
      cases op
      case boolNot => simp [sourceUnary?] at selected
      case wordNot => simp [sourceUnary?] at selected
      case wordClz => exact aRenderIH_clz operandIH
      all_goals exact aRenderIH_rejected _ fun _ _ => Or.inl rfl

theorem aRenderIH_binary {op : Solcore.Core.Wire.BinaryOp} {left right : CoreExpr}
    (leftIH : ARenderIH left) (rightIH : ARenderIH right) : ARenderIH (.binary op left right) := by
  cases selected : sourceBinary? op with
  | some _ => exact aRenderIH_binarySource selected leftIH rightIH
  | none =>
      cases extended : primitiveBinary? op with
      | some _ => exact aRenderIH_binaryPrimitive extended leftIH rightIH
      | none =>
          cases op <;> first
            | exact aRenderIH_rejected _ fun _ _ => Or.inl rfl
            | (simp [sourceBinary?] at selected; done)
            | (simp [primitiveBinary?] at extended; done)

theorem aRenderIH_applyAny {function argument : CoreExpr} (argumentIH : ARenderIH argument) :
    ARenderIH (.apply function argument) := by
  cases function
  case var index => exact aRenderIH_apply argumentIH
  all_goals exact aRenderIH_rejected _ fun _ _ => Or.inl rfl

theorem aRenderIH_loadCellAny {reference : CoreExpr} : ARenderIH (.loadCell reference) := by
  cases reference
  case var index => exact aRenderIH_loadCell index
  all_goals exact aRenderIH_rejected _ fun _ _ => Or.inl rfl

theorem aRenderIH_storeCellAny {reference value : CoreExpr} (valueIH : ARenderIH value) :
    ARenderIH (.storeCell reference value) := by
  cases reference
  case var index => exact aRenderIH_storeCell index valueIH
  all_goals exact aRenderIH_rejected _ fun _ _ => Or.inl rfl

theorem aRenderIH_newCell (elementType : Solcore.Core.Wire.Ty) (inner : CoreExpr) :
    ARenderIH (.newCell elementType inner) := by
  refine aRenderIH_rejected _ fun locals prior => ?_
  cases found : initializerKind? locals prior (.newCell elementType inner) with
  | none => exact Or.inl rfl
  | some kind =>
      right
      cases elementType
      all_goals first
        | rw [(AggregateKinds.newCell found).1]
        | cases found

/-- Every expression that the aggregate profile accepts and the actual
renderer renders satisfies its rendering specification. The second component
is the specification for the initializer of a direct `newCell` let. -/
theorem aggregate_render_spec : (expression : CoreExpr) →
    ARenderIH expression ∧ ∀ inner, expression = .newCell .word inner → ARenderIH inner
  | .word value => ⟨aRenderIH_word value, fun _ same => by cases same⟩
  | .bool value => ⟨aRenderIH_bool value, fun _ same => by cases same⟩
  | .unit => ⟨aRenderIH_unit, fun _ same => by cases same⟩
  | .var index => ⟨aRenderIH_var index, fun _ same => by cases same⟩
  | .letE initializer body =>
      ⟨aRenderIH_let (aggregate_render_spec initializer).1 (aggregate_render_spec initializer).2
        (aggregate_render_spec body).1, fun _ same => by cases same⟩
  | .ifE condition yes no =>
      ⟨aRenderIH_ifE (aggregate_render_spec condition).1 (aggregate_render_spec yes).1
        (aggregate_render_spec no).1, fun _ same => by cases same⟩
  | .pair left right =>
      ⟨aRenderIH_pair (aggregate_render_spec left).1 (aggregate_render_spec right).1,
        fun _ same => by cases same⟩
  | .first operand => ⟨aRenderIH_first (aggregate_render_spec operand).1,
      fun _ same => by cases same⟩
  | .second operand => ⟨aRenderIH_second (aggregate_render_spec operand).1,
      fun _ same => by cases same⟩
  | .inLeft _ payload => ⟨aRenderIH_inLeft (aggregate_render_spec payload).1,
      fun _ same => by cases same⟩
  | .inRight _ payload => ⟨aRenderIH_inRight (aggregate_render_spec payload).1,
      fun _ same => by cases same⟩
  | .caseE scrutinee yes no =>
      ⟨aRenderIH_caseE (aggregate_render_spec scrutinee).1 (aggregate_render_spec yes).1
        (aggregate_render_spec no).1, fun _ same => by cases same⟩
  | .unary _ operand => ⟨aRenderIH_unary (aggregate_render_spec operand).1,
      fun _ same => by cases same⟩
  | .binary _ left right =>
      ⟨aRenderIH_binary (aggregate_render_spec left).1 (aggregate_render_spec right).1,
        fun _ same => by cases same⟩
  | .ternary _ one two three =>
      ⟨aRenderIH_ternary (aggregate_render_spec one).1 (aggregate_render_spec two).1
        (aggregate_render_spec three).1, fun _ same => by cases same⟩
  | .apply _ argument => ⟨aRenderIH_applyAny (aggregate_render_spec argument).1,
      fun _ same => by cases same⟩
  | .newCell elementType inner => ⟨aRenderIH_newCell elementType inner, fun _ same => by
      cases same
      exact (aggregate_render_spec inner).1⟩
  | .loadCell _ => ⟨aRenderIH_loadCellAny, fun _ same => by cases same⟩
  | .storeCell _ value => ⟨aRenderIH_storeCellAny (aggregate_render_spec value).1,
      fun _ same => by cases same⟩
  | .integer _ => ⟨aRenderIH_rejected _ fun _ _ => Or.inl rfl, fun _ same => by cases same⟩
  | .lambda _ _ _ => ⟨aRenderIH_rejected _ fun _ _ => Or.inl rfl, fun _ same => by cases same⟩
  | .construct _ _ => ⟨aRenderIH_rejected _ fun _ _ => Or.inl rfl, fun _ same => by cases same⟩
  | .matchData _ _ _ _ =>
      ⟨aRenderIH_rejected _ fun _ _ => Or.inl rfl, fun _ same => by cases same⟩

end Solcore.Synthesis.Source.ScalarMeaning

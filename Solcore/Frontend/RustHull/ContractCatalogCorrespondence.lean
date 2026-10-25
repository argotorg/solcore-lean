import Solcore.Frontend.RustHull.RuntimeObjectLocationsCorrespondence

/-! Public compilation selects every catalog frame and installs its actual
closure. These facts retain the ordering used by the runtime dispatcher. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractCatalogCorrespondence
open Correspondence ScalarExecution CodeBuilder

def slots (codeBytes : Option (List UInt8)) (catalog : List AccountRuntime.CodeDefinition) :
    List (String × Core.Ty) :=
  Effects.slots ++ if codeBytes.isSome || !catalog.isEmpty then Effects.codeSlots else []

def images (codeBytes : Option (List UInt8)) (catalog : List AccountRuntime.CodeDefinition) :
    List (Nat × List UInt8) :=
  codeBytes.toList.map (1, ·) ++ catalog.zipIdx.filterMap fun (definition, index) =>
    if definition.isInit then none else some (index + 2, definition.bytes)

def compileDefinition (slotTypes : List (String × Core.Ty)) (fuel : Nat)
    (definition : AccountRuntime.CodeDefinition) : LowerM Core.Expr := do
  AccountRuntime.compileFrame definition.program
    (← AccountRuntime.select definition.program.objects definition.path) slotTypes fuel

inductive CompiledCatalog (slotTypes : List (String × Core.Ty)) (fuel : Nat) :
    List AccountRuntime.CodeDefinition → List Core.Expr → Prop where
  | nil : CompiledCatalog slotTypes fuel [] []
  | cons {definition : AccountRuntime.CodeDefinition} {code : CodeBlock} {compiled : Core.Expr}
      {definitions : List AccountRuntime.CodeDefinition} {expressions : List Core.Expr}
      (selected : AccountRuntime.select definition.program.objects definition.path = .ok code)
      (accepted : AccountRuntime.compileFrame definition.program code slotTypes fuel = .ok compiled)
      (tail : CompiledCatalog slotTypes fuel definitions expressions) :
      CompiledCatalog slotTypes fuel (definition :: definitions) (compiled :: expressions)

theorem compiledCatalog {slotTypes : List (String × Core.Ty)} {fuel : Nat}
    {catalog : List AccountRuntime.CodeDefinition} {expressions : List Core.Expr}
    (accepted : catalog.mapM (compileDefinition slotTypes fuel) = .ok expressions) :
    CompiledCatalog slotTypes fuel catalog expressions := by
  induction catalog generalizing expressions with
  | nil => cases accepted; exact .nil
  | cons definition definitions ih =>
      simp only [List.mapM_cons] at accepted
      obtain ⟨expression, head, accepted⟩ := lower_bind_eq_ok.mp accepted
      obtain ⟨rest, tail, returned⟩ := lower_bind_eq_ok.mp accepted
      cases returned
      obtain ⟨code, selected, accepted⟩ := lower_bind_eq_ok.mp head
      exact .cons selected accepted (ih tail)

theorem CompiledCatalog.length {slotTypes : List (String × Core.Ty)} {fuel : Nat}
    {catalog : List AccountRuntime.CodeDefinition} {expressions : List Core.Expr}
    (accepted : CompiledCatalog slotTypes fuel catalog expressions) : expressions.length = catalog.length := by
  induction accepted with
  | nil => rfl
  | cons _ _ _ ih => exact congrArg Nat.succ ih

theorem CompiledCatalog.selected {slotTypes : List (String × Core.Ty)} {fuel : Nat}
    {catalog : List AccountRuntime.CodeDefinition} {expressions : List Core.Expr}
    (accepted : CompiledCatalog slotTypes fuel catalog expressions)
    {index : Nat} {definition : AccountRuntime.CodeDefinition}
    (found : catalog[index]? = some definition) :
    ∃ code compiled, expressions[index]? = some compiled ∧
      AccountRuntime.select definition.program.objects definition.path = .ok code ∧
      AccountRuntime.compileFrame definition.program code slotTypes fuel = .ok compiled := by
  induction accepted generalizing index with
  | nil => simp at found
  | @cons head code compiled definitions rest selected accepted tail ih =>
      cases index with
      | zero =>
          have same : head = definition := Option.some.inj found
          subst definition
          exact ⟨code, compiled, rfl, selected, accepted⟩
      | succ index => exact ih found

theorem CompiledCatalog.captures {slotTypes : List (String × Core.Ty)} {fuel : Nat}
    {catalog : List AccountRuntime.CodeDefinition} {expressions : List Core.Expr}
    (accepted : CompiledCatalog slotTypes fuel catalog expressions) (environment : Core.Environment) :
    ∃ values, CapturedClosures environment expressions values := by
  induction accepted with
  | nil => exact ⟨[], .nil⟩
  | cons _ accepted _ ih =>
      obtain ⟨value, captured⟩ := compileFrame_captures accepted environment
      obtain ⟨values, captures⟩ := ih
      exact ⟨value :: values, .cons captured captures⟩

theorem captured_length {environment : Core.Environment} {expressions : List Core.Expr}
    {values : List Core.Value} (captured : CapturedClosures environment expressions values) :
    values.length = expressions.length := by
  induction captured with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem captured_selected {environment : Core.Environment} {expressions : List Core.Expr}
    {values : List Core.Value} (captured : CapturedClosures environment expressions values)
    {index : Nat} {expression : Core.Expr} (found : expressions[index]? = some expression) :
    ∃ value, values[index]? = some value ∧ CapturedClosure expression environment value := by
  induction captured generalizing index with
  | nil => simp at found
  | @cons head rest value values captured tail ih =>
      cases index with
      | zero =>
          have same : head = expression := Option.some.inj found
          subst expression
          exact ⟨value, rfl, captured⟩
      | succ index => exact ih found

/-- Every catalog entry is compiled in order with exactly the entry frame's
extended slot list, including entries used only as creation templates. -/
theorem compileObject_selected {program : Program} {path : List String} {code : CodeBlock}
    {fuel : Nat} {codeBytes : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    {expression : Core.Expr}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : AccountRuntime.compileObject program path fuel codeBytes catalog = .ok expression) :
    ∃ compiled others,
      AccountRuntime.compileFrame program code (slots codeBytes catalog) fuel = .ok compiled ∧
      catalog.mapM (compileDefinition (slots codeBytes catalog) fuel) = .ok others ∧
      expression = AccountRuntime.objectExpression (slots codeBytes catalog)
        compiled others (images codeBytes catalog) codeBytes catalog := by
  unfold AccountRuntime.compileObject at accepted
  obtain ⟨selectedCode, selectedAgain, accepted⟩ := lower_bind_eq_ok.mp accepted
  have same := Except.ok.inj (selectedAgain.symm.trans selected)
  subst selectedCode
  obtain ⟨compiled, compiledOk, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨others, mapped, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨guard, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  cases guard
  cases accepted
  exact ⟨compiled, others, compiledOk, mapped, rfl⟩

/-- Compilation itself supplies all closure-capture premises needed by the
generic object initializer; callers do not assume evaluation of a catalog. -/
theorem compileObject_captures {program : Program} {path : List String} {code : CodeBlock}
    {fuel : Nat} {codeBytes : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    {expression : Core.Expr}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : AccountRuntime.compileObject program path fuel codeBytes catalog = .ok expression)
    (environment : Core.Environment) :
    ∃ compiled others closure values,
      AccountRuntime.compileFrame program code (slots codeBytes catalog) fuel = .ok compiled ∧
      CompiledCatalog (slots codeBytes catalog) fuel catalog others ∧
      CapturedClosure compiled environment closure ∧
      CapturedClosures environment others values ∧
      CapturedClosures environment (compiled :: others) (closure :: values) ∧
      values.length = catalog.length ∧
      expression = AccountRuntime.objectExpression (slots codeBytes catalog)
        compiled others (images codeBytes catalog) codeBytes catalog := by
  obtain ⟨compiled, others, frame, mapped, expression⟩ := compileObject_selected selected accepted
  have catalogCompiled := compiledCatalog mapped
  obtain ⟨closure, captured⟩ := compileFrame_captures frame environment
  obtain ⟨values, captures⟩ := catalogCompiled.captures environment
  exact ⟨compiled, others, closure, values, frame, catalogCompiled, captured, captures,
    .cons captured captures, (captured_length captures).trans catalogCompiled.length, expression⟩

/-- The top-level frame is index zero of the actual closure packet. -/
theorem entry_reference {depth : Nat} {environment captured : Core.Environment}
    {functions : Code} {closure : Core.Value} {values : List Core.Value} {others : List Core.Expr}
    (catalogCaptured : CapturedClosures captured others values)
    (functionsRelated : CodeValue depth environment functions (bundleValues (closure :: values))) :
    CodeValue depth environment (part 0 (others.length + 1) functions) closure := by
  have selected := functionsRelated.part (index := 0) rfl
  simpa only [List.length_cons, captured_length catalogCaptured] using selected

/-- Catalog index `index` is installed after the entry closure, at runtime
packet index `index + 1`, with its own selected program and capture. -/
theorem catalog_reference {slotTypes : List (String × Core.Ty)} {fuel depth : Nat}
    {catalog : List AccountRuntime.CodeDefinition} {others : List Core.Expr}
    {environment captured : Core.Environment} {functions : Code}
    {closure : Core.Value} {values : List Core.Value}
    (compiled : CompiledCatalog slotTypes fuel catalog others)
    (catalogCaptured : CapturedClosures captured others values)
    (functionsRelated : CodeValue depth environment functions (bundleValues (closure :: values)))
    {index : Nat} {definition : AccountRuntime.CodeDefinition} (found : catalog[index]? = some definition) :
    ∃ code expression value,
      AccountRuntime.select definition.program.objects definition.path = .ok code ∧
      AccountRuntime.compileFrame definition.program code slotTypes fuel = .ok expression ∧
      CapturedClosure expression captured value ∧
      CodeValue depth environment (part (index + 1) (others.length + 1) functions) value := by
  obtain ⟨code, expression, expressionFound, selected, accepted⟩ := compiled.selected found
  obtain ⟨value, valueFound, captured⟩ := captured_selected catalogCaptured expressionFound
  refine ⟨code, expression, value, selected, accepted, captured, ?_⟩
  have projected := functionsRelated.part (index := index + 1) valueFound
  simpa only [List.length_cons, captured_length catalogCaptured] using projected

end Solcore.Frontend.RustHull.ContractCatalogCorrespondence

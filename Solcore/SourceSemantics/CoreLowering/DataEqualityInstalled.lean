import Solcore.SourceSemantics.CoreLowering.DataEqualityInitializationStore

/-! Exact closure layout during comparison helper installation. Each preceding
write introduces a real Unit binder. The installed closure stores the shifted
body together with that actual captured environment. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataEqualityInstalled
open Core Frontend SourceCoreDataEquality

def offset (count : Nat) : Renaming := fun index => count + index

def captured (count : Nat) (environment : Environment) : Environment :=
  List.replicate count .unit ++ environment

def helper (environment : Environment) (body : Expr) (index : Nat) : Value :=
  .closure (.product (.namedData ⟨index⟩) (.namedData ⟨index⟩)) .bool
    (body.rename (offset index).lift) (captured index environment)

def cells (environment : Environment) (bodies : List Expr) (start : Nat := 0) : List Value :=
  (bodies.zipIdx start).map fun (body, index) => .inRight .unit (helper environment body index)

/-- All catalog references are allocated before any closure is installed. -/
def References (catalog : Catalog) (base : Nat) (environment : Environment) : Prop :=
  ∀ index, index < catalog.entries.length →
    environment[referenceIndex catalog 0 ⟨index⟩]? =
      some (.cellRef (OptionalCell.cellType (comparatorType (.namedData ⟨index⟩))) (base + index))

private theorem captured_succ (count : Nat) (environment : Environment) :
    captured (count + 1) environment = .unit :: captured count environment := by
  simp [captured, List.replicate_succ]

private theorem offset_weaken (expression : Expr) (count : Nat) :
    (expression.weakenAt 0).rename (offset count).lift = expression.rename (offset (count + 1)) := by
  rw [← Expr.rename_insertion, Expr.rename_comp]
  congr 1
  funext index
  simp only [Renaming.comp, Renaming.insertion, Nat.zero_le, ↓reduceIte, Renaming.lift, offset]
  omega

private theorem captured_lookup {environment : Environment} {index count : Nat} {value : Value}
    (found : environment[index]? = some value) : (captured count environment)[count + index]? = some value := by
  simpa [captured, List.getElem?_append_right] using found

private theorem write_next (before previous remaining : Store) (old value : Value) :
    (before ++ previous ++ old :: remaining).write? (before.length + previous.length) value =
      some (before ++ previous ++ value :: remaining) := by
  have bound : before.length + previous.length < (before ++ previous ++ old :: remaining).length := by simp
  rw [Store.write?, if_pos bound]
  congr 1
  rw [List.set_append_right _ _ (by simp), List.length_append, Nat.sub_self]
  rfl

private def installRow (catalog : Catalog) (row : Expr × Nat) (next : Expr) : Expr :=
  .letE (.storeCell (.var (referenceIndex catalog 0 ⟨row.2⟩))
    (.inRight .unit (.lambda (.product (.namedData ⟨row.2⟩) (.namedData ⟨row.2⟩)) .bool row.1)))
    (next.weakenAt 0)

/-- Install an actual suffix of the generated rows. The relation specifies
both every stored closure and the final comparator's captured environment. -/
theorem install_evaluates_suffix (catalog : Catalog) (environment : Environment) (before : Store)
    (references : References catalog before.length environment)
    (remaining : List Expr) (count : Nat) (previous pending : Store)
    (previousLength : previous.length = count) (pendingLength : pending.length = remaining.length)
    (bounds : count + remaining.length ≤ catalog.entries.length)
    (parameter result : Ty) (body : Expr) :
    Evaluates (captured count environment) (before ++ previous ++ pending)
      (((remaining.zipIdx count).foldr (installRow catalog) (.lambda parameter result body)).rename (offset count))
      (.closure parameter result (body.rename (offset (count + remaining.length)).lift)
        (captured (count + remaining.length) environment))
      (before ++ previous ++ cells environment remaining count) := by
  induction remaining generalizing count previous pending with
  | nil =>
    cases pending with
    | nil => simpa [cells, offset, Expr.rename] using
        (Evaluates.lambda (environment := captured count environment) (store := before ++ previous)
          (parameterType := parameter) (resultType := result) (body := body.rename (offset count).lift))
    | cons => simp at pendingLength
  | cons head tail ih =>
    cases pending with
    | nil => simp at pendingLength
    | cons old pending =>
      have pendingTail : pending.length = tail.length := by simpa using pendingLength
      have previousNext : (previous ++ [Value.inRight .unit (helper environment head count)]).length = count + 1 := by simp [previousLength]
      have countEq : count + 1 + tail.length = count + (head :: tail).length := by
        simp only [List.length_cons, Nat.add_assoc]
        rw [Nat.add_comm 1 tail.length]
      have boundsNext : count + 1 + tail.length ≤ catalog.entries.length := countEq ▸ bounds
      have headBound : count < catalog.entries.length :=
        Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.zero_lt_succ tail.length)) bounds
      have evaluated := ih (count + 1) (previous ++ [Value.inRight .unit (helper environment head count)]) pending
        previousNext pendingTail boundsNext
      rw [countEq] at evaluated
      rw [List.zipIdx_cons, List.foldr_cons]
      simp only [installRow, Expr.rename]
      rw [offset_weaken]
      apply Evaluates.letE (bodyStore := before ++ previous ++ .inRight .unit (helper environment head count) :: pending)
      · apply Evaluates.storeCell
          (elementType := OptionalCell.cellType (comparatorType (.namedData ⟨count⟩)))
          (location := before.length + count) (oldValue := old)
        · exact .var (captured_lookup (references count headBound))
        · simp [Store.read?, ← previousLength]
        · exact .inRight .lambda
        · simpa only [previousLength, helper] using write_next before previous pending old (.inRight .unit (helper environment head count))
      · simpa [captured_succ, cells, List.zipIdx_cons, List.append_assoc, Nat.add_assoc, helper] using evaluated

/-- Actual `install` has this layout, including the Unit binders accumulated
by its preceding writes. No installed lambda body is executed here. -/
theorem install_evaluates (catalog : Catalog) (environment : Environment) (before pending : Store)
    (bodies : List Expr) (references : References catalog before.length environment)
    (pendingLength : pending.length = bodies.length) (bounds : bodies.length ≤ catalog.entries.length)
    (parameter result : Ty) (body : Expr) :
    Evaluates environment (before ++ pending) (install catalog bodies (.lambda parameter result body))
      (.closure parameter result (body.rename (offset bodies.length).lift) (captured bodies.length environment))
      (before ++ cells environment bodies) := by
  have evaluated := install_evaluates_suffix catalog environment before references bodies 0 [] pending rfl pendingLength
    (by simpa using bounds) parameter result body
  have zero : offset 0 = Renaming.id := by funext index; simp [offset, Renaming.id]
  rw [zero, Expr.rename_id] at evaluated
  simp only [captured, List.replicate_zero, List.nil_append, List.append_nil, Nat.zero_add] at evaluated
  exact evaluated

def catalogTypes (catalog : Catalog) : List Ty :=
  catalog.entries.zipIdx.map fun (_, index) => comparatorType (.namedData ⟨index⟩)

def emptyCells (types : List Ty) : Store := types.map fun type => .inLeft type .unit

def allocatedReferences (types : List Ty) (base : Nat) : Environment :=
  (types.zipIdx base).map fun (type, location) => .cellRef (OptionalCell.cellType type) location

def allocatedEnvironment (catalog : Catalog) (base : Nat) (environment : Environment) : Environment :=
  (allocatedReferences (catalogTypes catalog) base).reverse ++ environment

private theorem allocate_types_evaluates (types : List Ty) (next : Expr)
    (environment : Environment) (store : Store) {value : Value} {finalStore : Store}
    (nextEvaluated : Evaluates ((allocatedReferences types store.length).reverse ++ environment)
      (store ++ emptyCells types) next value finalStore) :
    Evaluates environment store
      (types.foldr (fun type body => .letE (OptionalCell.allocate type) body) next) value finalStore := by
  induction types generalizing environment store with
  | nil => simpa [allocatedReferences, emptyCells] using nextEvaluated
  | cons type types ih =>
    apply Evaluates.letE (OptionalCell.allocate_evaluates type environment store)
    apply ih
    simpa [allocatedReferences, emptyCells, List.zipIdx_cons, List.reverse_cons, List.append_assoc] using nextEvaluated

private theorem allocate_eq_types (catalog : Catalog) (next : Expr) :
    allocate catalog next =
      (catalogTypes catalog).foldr (fun type body => .letE (OptionalCell.allocate type) body) next := by
  simp [allocate, catalogTypes, List.foldr_map]

private theorem catalogTypes_length (catalog : Catalog) : (catalogTypes catalog).length = catalog.entries.length := by
  simp [catalogTypes]

private theorem allocated_references (catalog : Catalog) (base : Nat) (environment : Environment) :
    References catalog base (allocatedEnvironment catalog base environment) := by
  intro index bound
  have typesLength := catalogTypes_length catalog
  have referencesLength : (allocatedReferences (catalogTypes catalog) base).length = catalog.entries.length := by
    simp [allocatedReferences, typesLength]
  have typeFound : (catalogTypes catalog)[index]? = some (comparatorType (.namedData ⟨index⟩)) := by
    simp [catalogTypes, List.getElem?_zipIdx, List.getElem?_eq_getElem bound]
  have referenceFound : (allocatedReferences (catalogTypes catalog) base)[index]? =
      some (.cellRef (OptionalCell.cellType (comparatorType (.namedData ⟨index⟩))) (base + index)) := by
    simp [allocatedReferences, List.getElem?_zipIdx, typeFound]
  have reverseFound : (allocatedReferences (catalogTypes catalog) base).reverse[catalog.entries.length - 1 - index]? =
      some (.cellRef (OptionalCell.cellType (comparatorType (.namedData ⟨index⟩))) (base + index)) := by
    rw [List.getElem?_reverse' (j := index) (by omega)]
    exact referenceFound
  have reversedBound : catalog.entries.length - 1 - index < (allocatedReferences (catalogTypes catalog) base).reverse.length := by
    simp only [List.length_reverse, referencesLength]
    omega
  simpa [allocatedEnvironment, referenceIndex, List.getElem?_append_left reversedBound] using reverseFound

private theorem bodies_length {catalog : Catalog} {fuel : Nat} {bodies : List Expr}
    (generated : helperBodies fuel catalog = .ok bodies) : bodies.length = catalog.entries.length := by
  unfold helperBodies at generated
  have mapLength : ∀ (entries : List (SourceCoreDataCatalog.Entry × Nat)) (output : List Expr),
      entries.mapM (fun (_, index) => helperBody fuel catalog ⟨index⟩) = .ok output → output.length = entries.length := by
    intro entries
    induction entries with
    | nil => intro output accepted; simpa [List.mapM_nil, pure, Except.pure] using congrArg List.length (Except.ok.inj accepted).symm
    | cons head tail ih =>
      intro output accepted
      rw [List.mapM_cons] at accepted
      cases first : helperBody fuel catalog ⟨head.2⟩ with
      | error error => simp [first, bind, Except.bind] at accepted
      | ok value =>
        cases rest : tail.mapM (fun (_, index) => helperBody fuel catalog ⟨index⟩) with
        | error error => simp [first, rest, bind, Except.bind] at accepted
        | ok values =>
          simp only [first, rest, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
          subst output
          simpa using ih values rest
  simpa using mapLength _ _ generated

/-- The full generated initializer has an exact closure/store description.
Every helper captures all references plus the Unit binders created before its
own installation; the returned comparator captures all installation binders. -/
theorem prepared_evaluates_exact {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (environment : Environment) (store : Store) :
    Evaluates environment store prepared.expression
      (.closure (.product prepared.type prepared.type) .bool
        (prepared.body.rename (offset prepared.bodies.length).lift)
        (captured prepared.bodies.length (allocatedEnvironment checked.catalog store.length environment)))
      (store ++ cells (allocatedEnvironment checked.catalog store.length environment) prepared.bodies) := by
  rw [prepared.expression_eq, allocate_eq_types]
  apply allocate_types_evaluates
  apply install_evaluates checked.catalog _ store _ prepared.bodies
  · exact allocated_references _ _ _
  · simp [emptyCells, catalogTypes_length, bodies_length prepared.bodiesGenerated]
  · exact Nat.le_of_eq (bodies_length prepared.bodiesGenerated)

/-- Exact contents of each installed helper slot. The representation includes
real shifted code and actual captured environments, not merely a function type. -/
def Installed (catalog : Catalog) (bodies : List Expr) (base : Nat)
    (environment : Environment) (store : Store) : Prop :=
  ∀ index body, bodies[index]? = some body →
    store.read? (base + index) =
      some (.inRight .unit (helper (allocatedEnvironment catalog base environment) body index))

private theorem cells_lookup {environment : Environment} {bodies : List Expr} {index : Nat} {body : Expr}
    (found : bodies[index]? = some body) :
    (cells environment bodies)[index]? = some (.inRight .unit (helper environment body index)) := by
  simp [cells, List.getElem?_zipIdx, found]

theorem prepared_installed {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (environment : Environment) (store : Store) :
    Installed checked.catalog prepared.bodies store.length environment
      (store ++ cells (allocatedEnvironment checked.catalog store.length environment) prepared.bodies) := by
  intro index body found
  simpa [Store.read?, List.getElem?_append_right] using
    (cells_lookup (environment := allocatedEnvironment checked.catalog store.length environment) found)

/-- Helpers' captured references include their own cell and every other
catalog helper. Lookup remains exact despite earlier installation Unit binders. -/
theorem captured_reference (catalog : Catalog) (base : Nat) (environment : Environment)
    (count index : Nat) (bound : index < catalog.entries.length) :
    (captured count (allocatedEnvironment catalog base environment))[count + referenceIndex catalog 0 ⟨index⟩]? =
      some (.cellRef (OptionalCell.cellType (comparatorType (.namedData ⟨index⟩))) (base + index)) :=
  captured_lookup (allocated_references catalog base environment index bound)

/-- Every completed run of actual preparation installs the exact helper table;
finite completion itself follows from `prepared_evaluates_exact`. -/
theorem prepared_completed_installed {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {environment : Environment} {store finalStore : Store} {value : Value} {fuel : Nat}
    (ran : runStateful fuel (.initial prepared.expression environment store) = .done value finalStore) :
    value = .closure (.product prepared.type prepared.type) .bool
      (prepared.body.rename (offset prepared.bodies.length).lift)
      (captured prepared.bodies.length (allocatedEnvironment checked.catalog store.length environment)) ∧
    finalStore = store ++ cells (allocatedEnvironment checked.catalog store.length environment) prepared.bodies ∧
    Installed checked.catalog prepared.bodies store.length environment finalStore := by
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic (runStateful_evaluation_sound ran)
    (prepared_evaluates_exact prepared environment store)
  exact ⟨rfl, rfl, prepared_installed prepared environment store⟩

end Solcore.SourceSemantics.CoreLowering.DataEqualityInstalled

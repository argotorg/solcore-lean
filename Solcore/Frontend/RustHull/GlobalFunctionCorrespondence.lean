import Solcore.Frontend.RustHull.FunctionAssemblyCorrespondence
import Solcore.Frontend.RustHull.ParameterRenamingCorrespondence

/-! The allocation and installation folds used by assemble for arbitrary
function lists. Installed closures retain the administrative Unit binders
introduced by earlier stores; their bodies and environments are shifted
together. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence

def globalAllocation (signatures : List Signature) (body : Core.Expr) : Core.Expr :=
  signatures.foldr (fun signature next =>
    .letE (Core.OptionalCell.allocate signature.functionType) next) body

def globalEnvironment : List Signature → Nat → Core.Environment → Core.Environment
  | [], _, environment => environment
  | signature :: rest, location, environment =>
      globalEnvironment rest (location + 1)
        (.cellRef (Core.OptionalCell.cellType signature.functionType) location :: environment)

def globalStore (signatures : List Signature) (store : Core.Store) : Core.Store :=
  store ++ signatures.map (fun signature => .inLeft signature.functionType .unit)

theorem globalAllocation_evaluates {signatures : List Signature} {body : Core.Expr}
    {environment : Core.Environment} {initial final : Core.Store} {result : Core.Value}
    (evaluated : Core.Evaluates (globalEnvironment signatures initial.length environment)
      (globalStore signatures initial) body result final) :
    Core.Evaluates environment initial (globalAllocation signatures body) result final := by
  induction signatures generalizing environment initial with
  | nil => simpa [globalAllocation, globalEnvironment, globalStore] using evaluated
  | cons signature rest ih =>
      apply Core.Evaluates.letE (Core.OptionalCell.allocate_evaluates _ _ _)
      apply ih
      simpa [globalEnvironment, globalStore, List.append_assoc] using evaluated

theorem globalEnvironment_eq (signatures : List Signature) (base : Nat)
    (environment : Core.Environment) :
    globalEnvironment signatures base environment =
      ((signatures.zipIdx base).map (fun (signature, location) =>
        Core.Value.cellRef (Core.OptionalCell.cellType signature.functionType) location)).reverse ++ environment := by
  induction signatures generalizing base environment with
  | nil => rfl
  | cons signature rest ih =>
      simp [globalEnvironment, List.zipIdx_cons, ih, List.append_assoc]

/-- Every declared function receives a fresh cell, and globals appear in the
reverse order used by the actual compiler's lexical scope. -/
theorem globalEnvironment_lookup {signatures : List Signature} {index : Nat} {own : Signature}
    (found : signatures.reverse[index]? = some own) (base : Nat) (environment : Core.Environment) :
    (globalEnvironment signatures base environment)[index]? =
      some (.cellRef (Core.OptionalCell.cellType own.functionType)
        (base + (signatures.length - 1 - index))) := by
  have bound : index < signatures.length := by
    have := (List.getElem?_eq_some_iff.mp found).1
    simpa using this
  rw [globalEnvironment_eq, List.getElem?_append_left (by simpa using bound)]
  rw [List.getElem?_reverse (by simpa using bound), List.getElem?_map, List.getElem?_zipIdx]
  rw [List.getElem?_reverse bound] at found
  simp only [List.length_map, List.length_zipIdx, found, Option.map_some]

theorem globalStore_lookup {signatures : List Signature} {index : Nat} {own : Signature}
    (found : signatures.reverse[index]? = some own) (store : Core.Store) :
    (globalStore signatures store).read? (store.length + (signatures.length - 1 - index)) =
      some (.inLeft own.functionType .unit) := by
  have bound : index < signatures.length := by
    have := (List.getElem?_eq_some_iff.mp found).1
    simpa using this
  rw [List.getElem?_reverse bound] at found
  simp [globalStore, Core.Store.read?, List.getElem?_append_right, found]

structure GlobalCode where
  own : Signature
  body : Core.Expr

def GlobalCode.expression (code : GlobalCode) : Core.Expr :=
  .lambda (bundleType code.own.parameters) (Core.LanguageResult.resultType code.own.result) code.body

def globalShift (offsetCount : Nat) : Core.Renaming := fun index => offsetCount + index

def installationEnvironment (environment : Core.Environment) (offsetCount : Nat) : Core.Environment :=
  List.replicate offsetCount .unit ++ environment

def GlobalCode.installedValue (code : GlobalCode) (environment : Core.Environment) (offsetCount : Nat) : Core.Value :=
  .inRight .unit (.closure (bundleType code.own.parameters)
    (Core.LanguageResult.resultType code.own.result) (code.body.rename (globalShift offsetCount).lift)
    (installationEnvironment environment offsetCount))

def globalInstallation (codes : List GlobalCode) (start : Nat) (body : Core.Expr) : Core.Expr :=
  (codes.zipIdx start).foldr (fun (code, index) next =>
    .letE (.storeCell (.var index) (.inRight .unit code.expression)) (next.weakenAt 0)) body

def installationStore (locations : Nat → Nat) (environment : Core.Environment) :
    List GlobalCode → Nat → Nat → Core.Store → Core.Store
  | [], _, _, store => store
  | code :: rest, start, offsetCount, store =>
      installationStore locations environment rest (start + 1) (offsetCount + 1)
        (store.set (locations start) (code.installedValue environment offsetCount))

@[simp] theorem installationStore_length (locations : Nat → Nat) (environment : Core.Environment)
    (codes : List GlobalCode) (start offsetCount : Nat) (store : Core.Store) :
    (installationStore locations environment codes start offsetCount store).length = store.length := by
  induction codes generalizing start offsetCount store with
  | nil => rfl
  | cons code rest ih => simp [installationStore, ih]

theorem installationStore_preserves {locations : Nat → Nat} {environment : Core.Environment}
    {codes : List GlobalCode} {start offsetCount location : Nat} {store : Core.Store}
    (untouched : ∀ index, index < codes.length → locations (start + index) ≠ location) :
    (installationStore locations environment codes start offsetCount store).read? location = store.read? location := by
  induction codes generalizing start offsetCount store with
  | nil => rfl
  | cons code rest ih =>
      rw [installationStore, ih]
      · exact List.getElem?_set_ne (by simpa using untouched 0 (by simp))
      · intro index bound
        simpa only [Nat.add_assoc, Nat.add_comm 1 index] using untouched (index + 1) (by simpa using bound)

/-- All installed cells retain the exact closure body and capture environment
after the remaining registrations. Later installations cannot overwrite it. -/
theorem installationStore_lookup {locations : Nat → Nat} {environment : Core.Environment}
    {codes : List GlobalCode} {start offsetCount index : Nat} {code : GlobalCode} {store : Core.Store}
    (found : codes[index]? = some code)
    (bounded : ∀ offset, offset < codes.length → locations (start + offset) < store.length)
    (distinct : ∀ left right, left < codes.length → right < codes.length →
      locations (start + left) = locations (start + right) → left = right) :
    (installationStore locations environment codes start offsetCount store).read? (locations (start + index)) =
      some (code.installedValue environment (offsetCount + index)) := by
  induction codes generalizing start offsetCount index store with
  | nil => simp at found
  | cons head rest ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst head
          rw [installationStore, installationStore_preserves]
          · simpa only [Nat.add_zero, Core.Store.read?] using
              List.getElem?_set_self (l := store) (a := code.installedValue environment offsetCount)
                (by simpa using bounded 0 (by simp))
          · intro offset bound
            intro same
            have impossible := distinct (offset + 1) 0 (by simpa using bound) (by simp)
              (by simpa [Nat.add_assoc, Nat.add_comm 1 offset] using same)
            omega
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          rw [installationStore]
          have result := ih (start := start + 1) (offsetCount := offsetCount + 1)
            (store := store.set (locations start) (head.installedValue environment offsetCount)) found
            (fun offset bound => by
              simpa only [List.length_set, Nat.add_assoc, Nat.add_comm 1 offset] using
                bounded (offset + 1) (by simpa using bound))
            (fun left right leftBound rightBound equal => by
              have same := distinct (left + 1) (right + 1) (by simpa using leftBound)
                (by simpa using rightBound) (by simpa [Nat.add_assoc, Nat.add_comm 1] using equal)
              omega)
          simpa only [Nat.add_assoc, Nat.add_comm 1 index] using result

theorem installationEnvironment_succ (environment : Core.Environment) (offsetCount : Nat) :
    installationEnvironment environment (offsetCount + 1) =
      .unit :: installationEnvironment environment offsetCount := by
  simp [installationEnvironment, List.replicate_succ]

theorem installationEnvironment_lookup {environment : Core.Environment} {index : Nat} {value : Core.Value}
    (found : environment[index]? = some value) (offsetCount : Nat) :
    (installationEnvironment environment offsetCount)[globalShift offsetCount index]? = some value := by
  simp [installationEnvironment, globalShift, List.getElem?_append_right, found]

theorem globalShift_succ (offsetCount : Nat) :
    Core.Renaming.comp (Core.Renaming.insertion 0) (globalShift offsetCount) =
      globalShift (offsetCount + 1) := by
  funext index
  simp [Core.Renaming.comp, Core.Renaming.insertion, globalShift, Nat.add_assoc, Nat.add_comm 1 index]

theorem weaken_globalShift (expression : Core.Expr) (offsetCount : Nat) :
    (expression.weakenAt 0).rename (globalShift offsetCount).lift =
      expression.rename (globalShift (offsetCount + 1)) := by
  rw [← Core.Expr.rename_insertion, Core.Expr.rename_comp,
    Core.Renaming.lift_comp_insertion_zero, globalShift_succ]

/-- Execute every store in the compiler's installation fold, then the real
continuation. The store and all captured environments are computed from the
actual global references supplied by allocation. -/
theorem globalInstallation_evaluates {codes : List GlobalCode} {start offsetCount : Nat}
    {locations : Nat → Nat} {environment : Core.Environment} {store final : Core.Store}
    (references : ∀ index code, codes[index]? = some code →
      environment[start + index]? =
        some (.cellRef (Core.OptionalCell.cellType code.own.functionType) (locations (start + index))))
    (bounded : ∀ index, index < codes.length → locations (start + index) < store.length)
    {body : Core.Expr} {result : Core.Value}
    (evaluated : Core.Evaluates (installationEnvironment environment (offsetCount + codes.length))
      (installationStore locations environment codes start offsetCount store)
      (body.rename (globalShift (offsetCount + codes.length))) result final) :
    Core.Evaluates (installationEnvironment environment offsetCount) store
      ((globalInstallation codes start body).rename (globalShift offsetCount)) result final := by
  induction codes generalizing start offsetCount store with
  | nil => simpa [globalInstallation, installationStore] using evaluated
  | cons code rest ih =>
      have locationBound : locations start < store.length := by simpa using bounded 0 (by simp)
      have reference : environment[start]? =
          some (.cellRef (Core.OptionalCell.cellType code.own.functionType) (locations start)) := by
        simpa using references 0 code rfl
      have stored : Core.Evaluates (installationEnvironment environment offsetCount) store
          (.storeCell (.var (globalShift offsetCount start))
            (.inRight .unit (code.expression.rename (globalShift offsetCount)))) .unit
          (store.set (locations start) (code.installedValue environment offsetCount)) := by
        apply Core.Evaluates.storeCell
          (.var (installationEnvironment_lookup reference offsetCount))
          (show store.read? (locations start) = some store[locations start] from
            List.getElem?_eq_getElem locationBound)
          (.inRight .lambda)
        simp only [Core.Store.write?, locationBound, ↓reduceIte]
        rfl
      simp only [globalInstallation, List.zipIdx_cons, List.foldr_cons, Core.Expr.rename]
      apply Core.Evaluates.letE stored
      change Core.Evaluates (.unit :: installationEnvironment environment offsetCount)
        (store.set (locations start) (code.installedValue environment offsetCount))
        (((globalInstallation rest (start + 1) body).weakenAt 0).rename
          (globalShift offsetCount).lift) result final
      rw [weaken_globalShift, ← installationEnvironment_succ]
      apply ih
      · intro index tail found
        simpa only [Nat.add_assoc, Nat.add_comm 1 index] using references (index + 1) tail found
      · intro index bound
        simpa only [List.length_set, Nat.add_assoc, Nat.add_comm 1 index] using
          bounded (index + 1) (by simpa using bound)
      · simpa only [installationStore, List.length_cons, Nat.add_assoc,
          Nat.add_comm 1 rest.length] using evaluated

theorem globalInstallation_eq (codes : List GlobalCode) (start : Nat) (body : Core.Expr) :
    globalInstallation codes start body =
      ((codes.map GlobalCode.expression).zipIdx start).foldr (fun (closure, index) next =>
        .letE (.storeCell (.var index) (.inRight .unit closure)) (next.weakenAt 0)) body := by
  induction codes generalizing start with
  | nil => rfl
  | cons code rest ih =>
      simp only [globalInstallation, List.map_cons, List.zipIdx_cons, List.foldr_cons]
      rw [← ih]
      rfl

def CompiledGlobal (fuel : Nat) (signatures : List Signature) (scope : Scope)
    (item : Function × Signature) (code : GlobalCode) : Prop :=
  code.own = item.2 ∧ lowerFunction fuel signatures scope item.1 item.2 = .ok code.expression

inductive CompiledGlobals (fuel : Nat) (signatures : List Signature) (scope : Scope) :
    List (Function × Signature) → List GlobalCode → Prop where
  | nil : CompiledGlobals fuel signatures scope [] []
  | cons {item : Function × Signature} {code : GlobalCode}
      {items : List (Function × Signature)} {codes : List GlobalCode}
      (head : CompiledGlobal fuel signatures scope item code)
      (tail : CompiledGlobals fuel signatures scope items codes) :
      CompiledGlobals fuel signatures scope (item :: items) (code :: codes)

/-- Every accepted function lowerer produces a lambda, retaining its actual
parameter allocation and result wrapper inside the recorded body. -/
theorem lowerFunctions_codes {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {items : List (Function × Signature)} {closures : List Core.Expr}
    (compiled : items.mapM (fun (function, own) =>
      lowerFunction fuel signatures scope function own) = .ok closures) :
    ∃ codes, closures = codes.map GlobalCode.expression ∧
      CompiledGlobals fuel signatures scope items codes := by
  induction items generalizing closures with
  | nil => cases compiled; exact ⟨[], rfl, .nil⟩
  | cons item rest ih =>
      simp only [List.mapM_cons] at compiled
      obtain ⟨closure, closureCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨tail, tailCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      obtain ⟨codes, rfl, related⟩ := ih tailCompiled
      obtain ⟨statements, _, closureShape⟩ :=
        StatementCorrespondence.lowerFunction_components closureCompiled
      let code : GlobalCode := ⟨item.2,
        parameterCode item.2.parameters.length 0 item.2.parameters
          (StatementCorrespondence.finishedBody item.2.result statements)⟩
      have closureEqual : closure = code.expression := closureShape
      exact ⟨code :: codes, by simp only [List.map_cons, closureEqual],
        .cons ⟨rfl, closureEqual ▸ closureCompiled⟩ related⟩

def globalScope (signatures : List Signature) (runtime : Scope) : Scope :=
  (signatures.reverse.map fun signature =>
    ⟨some (Effects.slotName ("function$" ++ signature.name)), signature.functionType, true⟩) ++ runtime

def globalInvocation (own : Signature) (index globalCount runtimeCount : Nat) : Core.Expr :=
  Core.LanguageResult.bind own.result
    (Core.OptionalCell.read own.functionType (.var index) (Core.Word.ofNatModulo 1))
    (.apply (.var 0) (.var (globalCount + runtimeCount + 1)))

/-- Decompose the real assembler into the exact folds proved above. No
alternate allocation or installation path is substituted for its code. -/
theorem assemble_components {functions : List Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (compiled : assemble functions entry runtime fuel = .ok (own, allocated)) :
    ∃ signatures codes binding index,
      functions.mapM (signature fuel) = .ok signatures ∧
      signatures.find? (·.name == entry) = some own ∧
      CompiledGlobals fuel signatures (globalScope signatures runtime)
        (functions.zip signatures).reverse codes ∧
      (globalScope signatures runtime).lookup (Effects.slotName ("function$" ++ entry)) = .ok (binding, index) ∧
      allocated = globalAllocation signatures
        (globalInstallation codes 0 (globalInvocation own index signatures.length runtime.length)) := by
  by_cases unique : (functions.map (·.name)).eraseDups.length = functions.length
  · simp only [assemble, unique, ↓reduceIte] at compiled
    obtain ⟨signatures, signaturesCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases selected : signatures.find? (·.name == entry) with
    | none => simp [selected, fail, Bind.bind, Except.bind] at compiled
    | some own' =>
        simp only [selected, Pure.pure, Except.pure, Bind.bind, Except.bind] at compiled
        obtain ⟨closures, closuresCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
        obtain ⟨⟨binding, index⟩, looked, returned⟩ := lower_bind_eq_ok.mp compiled
        cases returned
        obtain ⟨codes, rfl, codesCompiled⟩ := lowerFunctions_codes closuresCompiled
        refine ⟨signatures, codes, binding, index, signaturesCompiled, selected, codesCompiled, looked, ?_⟩
        simp only [globalAllocation, globalInstallation_eq, globalInvocation, List.length_reverse]
  · simp [assemble, unique, fail, Bind.bind, Except.bind] at compiled

/-- Exact installed-closure lookup invariant. The environment here is the
global reference environment before the store-result Unit binders are added. -/
def InstalledGlobals (codes : List GlobalCode) (locations : Nat → Nat)
    (environment : Core.Environment) (store : Core.Store) : Prop :=
  ∀ index code, codes[index]? = some code →
    store.read? (locations index) = some (code.installedValue environment index)

theorem InstalledGlobals.append {codes : List GlobalCode} {locations : Nat → Nat}
    {environment : Core.Environment} {store : Core.Store}
    (installed : InstalledGlobals codes locations environment store) (suffix : Core.Store) :
    InstalledGlobals codes locations environment (store ++ suffix) := by
  intro index code found
  have looked := installed index code found
  have bound := (List.getElem?_eq_some_iff.mp looked).1
  simpa only [Core.Store.read?, List.getElem?_append_left bound] using looked

/-- Source values have no function-closure constructor. Consequently a source
local cell cannot alias an installed global function cell. -/
theorem ValueRel.not_closure {type : Core.Ty} {source : Semantics.Value}
    {parameterType resultType : Core.Ty} {body : Core.Expr} {environment : Core.Environment} :
    ¬ ValueRel type source (.closure parameterType resultType body environment) := by
  intro related
  cases related

theorem InstalledGlobals.write {codes : List GlobalCode} {locations : Nat → Nat}
    {environment : Core.Environment} {store updated : Core.Store}
    (installed : InstalledGlobals codes locations environment store)
    {world : World} {source : Semantics.Heap} (heap : HeapRel world source store)
    {index : Nat} {type : Core.Ty} {location : Nat} {value : Core.Value}
    (entry : world[index]? = some (type, location))
    (written : store.write? location value = some updated) :
    InstalledGlobals codes locations environment updated := by
  intro globalIndex code found
  have looked := installed globalIndex code found
  have different : locations globalIndex ≠ location := by
    intro sameLocation
    obtain ⟨sourceValue, targetValue, _, sourceRead, related⟩ := heap.cell index type location entry
    rw [sameLocation] at looked
    have sameValue := Option.some.inj (sourceRead.symm.trans looked)
    change Core.Value.inRight .unit targetValue =
      .inRight .unit (.closure (bundleType code.own.parameters)
        (Core.LanguageResult.resultType code.own.result)
        (code.body.rename (globalShift globalIndex).lift)
        (installationEnvironment environment globalIndex)) at sameValue
    cases sameValue
    exact ValueRel.not_closure related
  rw [Core.Store.write?_preserves_other written different]
  exact looked

theorem InstalledGlobals.externalFrame {σ : Type} (codes : List GlobalCode)
    (locations : Nat → Nat) (environment : Core.Environment) :
    StatementCorrespondence.ExternalFrame
      (fun (_ : σ) store => InstalledGlobals codes locations environment store) where
  allocate := fun installed => installed.append _
  write := fun installed heap entry written => installed.write heap entry written

theorem InstalledGlobals.of_installation {codes : List GlobalCode} {locations : Nat → Nat}
    {environment : Core.Environment} {store : Core.Store}
    (bounded : ∀ index, index < codes.length → locations index < store.length)
    (distinct : ∀ left right, left < codes.length → right < codes.length →
      locations left = locations right → left = right) :
    InstalledGlobals codes locations environment
      (installationStore locations environment codes 0 0 store) := by
  intro index code found
  simpa only [Nat.zero_add] using installationStore_lookup found
    (start := 0) (offsetCount := 0) (store := store)
    (by simpa only [Nat.zero_add] using bounded)
    (by simpa only [Nat.zero_add] using distinct)

theorem CompiledGlobals.signatures {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {items : List (Function × Signature)} {codes : List GlobalCode}
    (compiled : CompiledGlobals fuel signatures scope items codes) :
    codes.map GlobalCode.own = items.map Prod.snd := by
  induction compiled with
  | nil => rfl
  | cons head _ ih => simp only [List.map_cons, head.1, ih]

theorem signatures_length {fuel : Nat} {functions : List Function} {signatures : List Signature}
    (compiled : functions.mapM (signature fuel) = .ok signatures) :
    functions.length = signatures.length := by
  induction functions generalizing signatures with
  | nil => cases compiled; rfl
  | cons function rest ih =>
      simp only [List.mapM_cons] at compiled
      obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨tail, tailCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      exact congrArg Nat.succ (ih tailCompiled)

/-- The signatures retained by accepted closures are exactly the reversed
declaration signatures used by global scope and allocation. -/
theorem CompiledGlobals.aligned {fuel : Nat} {functions : List Function}
    {signatures : List Signature} {scope : Scope} {codes : List GlobalCode}
    (signaturesCompiled : functions.mapM (signature fuel) = .ok signatures)
    (compiled : CompiledGlobals fuel signatures scope (functions.zip signatures).reverse codes) :
    codes.map GlobalCode.own = signatures.reverse := by
  rw [compiled.signatures, List.map_reverse,
    List.map_snd_zip (Nat.le_of_eq (signatures_length signaturesCompiled).symm)]

/-- Global lexical bindings retain their actual internal names and cell
locations while source locals and administrative binders are added. -/
def GlobalEnvironmentRel (codes : List GlobalCode) (locations : Nat → Nat)
    (scope : Scope) (mapping : Core.Renaming) (environment : Core.Environment) : Prop :=
  ∀ index code, codes[index]? = some code → ∃ slot,
    scope.lookup (Effects.slotName ("function$" ++ code.own.name)) =
      .ok (⟨some (Effects.slotName ("function$" ++ code.own.name)), code.own.functionType, true⟩, slot) ∧
    environment[mapping slot]? = some (.cellRef (Core.OptionalCell.cellType code.own.functionType) (locations index))

theorem GlobalEnvironmentRel.lookup {codes : List GlobalCode} {locations : Nat → Nat}
    {scope : Scope} {mapping : Core.Renaming} {environment : Core.Environment}
    (related : GlobalEnvironmentRel codes locations scope mapping environment)
    {index : Nat} {code : GlobalCode} (found : codes[index]? = some code)
    {binding : Binding} {slot : Nat}
    (looked : scope.lookup (Effects.slotName ("function$" ++ code.own.name)) = .ok (binding, slot)) :
    binding.type = code.own.functionType ∧ binding.reference = true ∧
    environment[mapping slot]? = some (.cellRef (Core.OptionalCell.cellType code.own.functionType) (locations index)) := by
  obtain ⟨actualSlot, actual, reference⟩ := related index code found
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (looked.symm.trans actual))
  exact ⟨rfl, rfl, reference⟩

theorem GlobalEnvironmentRel.temporary {codes : List GlobalCode} {locations : Nat → Nat}
    {scope : Scope} {mapping : Core.Renaming} {environment : Core.Environment}
    (related : GlobalEnvironmentRel codes locations scope mapping environment)
    (type : Core.Ty) (value : Core.Value) :
    GlobalEnvironmentRel codes locations (scope.temporary type) mapping.lift (value :: environment) := by
  intro index code found
  obtain ⟨slot, looked, reference⟩ := related index code found
  refine ⟨slot + 1, ?_, reference⟩
  simp [Scope.temporary, scope_lookup_cons, looked]

theorem slotName_reserved (name : String) :
    (Effects.slotName name).startsWith Effects.reservedPrefix = true := by
  simp [Effects.slotName, String.startsWith_string_iff]

theorem GlobalEnvironmentRel.addLocal {codes : List GlobalCode} {locations : Nat → Nat}
    {scope : Scope} {mapping : Core.Renaming} {environment : Core.Environment}
    (related : GlobalEnvironmentRel codes locations scope mapping environment)
    (name : String) (type : Core.Ty) (value : Core.Value)
    (allowed : name.startsWith Effects.reservedPrefix = false) :
    GlobalEnvironmentRel codes locations (scope.addLocal name type) mapping.lift (value :: environment) := by
  intro index code found
  obtain ⟨slot, looked, reference⟩ := related index code found
  have different : name ≠ Effects.slotName ("function$" ++ code.own.name) := by
    intro same
    have reserved := slotName_reserved ("function$" ++ code.own.name)
    rw [← same, allowed] at reserved
    contradiction
  refine ⟨slot + 1, ?_, reference⟩
  simp [Scope.addLocal, scope_lookup_cons, different, looked]

theorem GlobalEnvironmentRel.prepend {codes : List GlobalCode} {locations : Nat → Nat}
    {scope : Scope} {mapping : Core.Renaming} {environment : Core.Environment}
    (related : GlobalEnvironmentRel codes locations scope mapping environment)
    (extra : Core.Environment) :
    GlobalEnvironmentRel codes locations scope (fun index => extra.length + mapping index) (extra ++ environment) := by
  intro index code found
  obtain ⟨slot, looked, reference⟩ := related index code found
  refine ⟨slot, looked, ?_⟩
  simpa only [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] using reference

def globalLocations (signatures : List Signature) (base : Nat) : Nat → Nat :=
  fun index => base + (signatures.length - 1 - index)

theorem GlobalEnvironmentRel.of_lookup {signatures : List Signature} {codes : List GlobalCode}
    (aligned : codes.map GlobalCode.own = signatures.reverse) {scope : Scope}
    (looked : ∀ index code, codes[index]? = some code →
      scope.lookup (Effects.slotName ("function$" ++ code.own.name)) =
        .ok (⟨some (Effects.slotName ("function$" ++ code.own.name)), code.own.functionType, true⟩, index))
    (base : Nat) (environment : Core.Environment) :
    GlobalEnvironmentRel codes (globalLocations signatures base) scope Core.Renaming.id
      (globalEnvironment signatures base environment) := by
  intro index code found
  refine ⟨index, looked index code found, ?_⟩
  apply globalEnvironment_lookup
  simp only [Core.Renaming.id, ← aligned, List.getElem?_map, found, Option.map_some]

theorem ParameterCells.globalEnvironment {types : List Core.Ty} {values : List Core.Value}
    {environment finalEnvironment : Core.Environment} {store finalStore : Core.Store}
    (cells : ParameterCells types values environment store finalEnvironment finalStore)
    {arguments : List Arg} (arity : arguments.length = types.length)
    (allowed : ∀ argument ∈ arguments, argument.name.startsWith Effects.reservedPrefix = false)
    {codes : List GlobalCode} {locations : Nat → Nat} {scope : Scope} {mapping : Core.Renaming}
    (related : GlobalEnvironmentRel codes locations scope mapping environment) :
    GlobalEnvironmentRel codes locations (parameterScope arguments types scope)
      (parameterRenaming types.length mapping) finalEnvironment := by
  induction cells generalizing arguments scope mapping with
  | nil =>
      have empty : arguments = [] := List.eq_nil_of_length_eq_zero arity
      subst arguments
      exact related
  | @cons type types value values environment store finalEnvironment finalStore rest ih =>
      cases arguments with
      | nil => simp at arity
      | cons argument arguments =>
          apply ih (Nat.succ.inj arity)
            (fun arg member => allowed arg (List.mem_cons_of_mem argument member))
          exact related.addLocal argument.name type
            (.cellRef (Core.OptionalCell.cellType type) store.length)
            (allowed argument (List.mem_cons_self ..))

theorem aligned_length {signatures : List Signature} {codes : List GlobalCode}
    (aligned : codes.map GlobalCode.own = signatures.reverse) : codes.length = signatures.length := by
  simpa only [List.length_map, List.length_reverse] using congrArg List.length aligned

theorem globalLocations_bounded {signatures : List Signature} {codes : List GlobalCode}
    (aligned : codes.map GlobalCode.own = signatures.reverse) (store : Core.Store)
    {index : Nat} (bound : index < codes.length) :
    globalLocations signatures store.length index < (globalStore signatures store).length := by
  have length := aligned_length aligned
  simp only [globalLocations, globalStore, List.length_append, List.length_map]
  omega

theorem globalLocations_distinct {signatures : List Signature} {codes : List GlobalCode}
    (aligned : codes.map GlobalCode.own = signatures.reverse) (base : Nat)
    {left right : Nat} (leftBound : left < codes.length) (rightBound : right < codes.length)
    (same : globalLocations signatures base left = globalLocations signatures base right) : left = right := by
  have length := aligned_length aligned
  simp only [globalLocations] at same
  omega

def initializedGlobals (signatures : List Signature) (codes : List GlobalCode)
    (environment : Core.Environment) (store : Core.Store) : Core.Store :=
  installationStore (globalLocations signatures store.length)
    (globalEnvironment signatures store.length environment) codes 0 0 (globalStore signatures store)

theorem InstalledGlobals.initialize {signatures : List Signature} {codes : List GlobalCode}
    (aligned : codes.map GlobalCode.own = signatures.reverse)
    (environment : Core.Environment) (store : Core.Store) :
    InstalledGlobals codes (globalLocations signatures store.length)
      (globalEnvironment signatures store.length environment)
      (initializedGlobals signatures codes environment store) := by
  apply InstalledGlobals.of_installation
  · intro index bound
    exact globalLocations_bounded aligned store bound
  · intro left right leftBound rightBound same
    exact globalLocations_distinct aligned store.length leftBound rightBound same

theorem HeapRel.initializeGlobals {world : World} {source : Semantics.Heap} {store : Core.Store}
    (related : HeapRel world source store) (signatures : List Signature) (codes : List GlobalCode)
    (environment : Core.Environment) :
    HeapRel world source (initializedGlobals signatures codes environment store) where
  length_eq := related.length_eq
  distinct := related.distinct
  cell := by
    intro index type location entry
    obtain ⟨sourceValue, targetValue, found, read, valueRelated⟩ := related.cell index type location entry
    refine ⟨sourceValue, targetValue, found, ?_, valueRelated⟩
    have bound := related.location_bound entry
    rw [initializedGlobals, installationStore_preserves]
    · simpa only [globalStore, Core.Store.read?, List.getElem?_append_left bound] using read
    · intro offset _
      simp only [globalLocations]
      omega

/-- Execute allocation and installation from an arbitrary real caller store.
The continuation receives exactly the registered closure invariant above. -/
theorem globalInitialization_evaluates {signatures : List Signature} {codes : List GlobalCode}
    (aligned : codes.map GlobalCode.own = signatures.reverse)
    {environment : Core.Environment} {initial final : Core.Store} {body : Core.Expr} {result : Core.Value}
    (evaluated : Core.Evaluates
      (installationEnvironment (globalEnvironment signatures initial.length environment) codes.length)
      (initializedGlobals signatures codes environment initial)
      (body.rename (globalShift codes.length)) result final) :
    Core.Evaluates environment initial
      (globalAllocation signatures (globalInstallation codes 0 body)) result final := by
  apply globalAllocation_evaluates
  have references : ∀ index code, codes[index]? = some code →
      (globalEnvironment signatures initial.length environment)[0 + index]? =
        some (.cellRef (Core.OptionalCell.cellType code.own.functionType)
          (globalLocations signatures initial.length (0 + index))) := by
    intro index code found
    apply globalEnvironment_lookup
    simp only [Nat.zero_add, ← aligned, List.getElem?_map, found, Option.map_some]
  have executed := globalInstallation_evaluates (start := 0) (offsetCount := 0)
    (store := globalStore signatures initial) (body := body) (result := result) (final := final) references
    (fun index bound => by simpa only [Nat.zero_add] using
      globalLocations_bounded aligned initial (index := index) bound)
    (by simpa only [Nat.zero_add, initializedGlobals] using evaluated)
  have zero : globalShift 0 = Core.Renaming.id := by funext index; simp [globalShift, Core.Renaming.id]
  simpa only [zero, Core.Expr.rename_id, installationEnvironment, List.replicate_zero,
    List.nil_append] using executed

end Solcore.Frontend.RustHull.Correspondence

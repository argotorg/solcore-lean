import Solcore.Frontend.SourceInference.TypedIR
import Solcore.Core.Syntax

/-! Raw source metadata carried by a source-compatible Core boundary.

Runtime type compatibility does not erase value identity: proxy equality and
constructor patterns compare the original metadata. This sealed registry
interns that metadata before native execution. Static entries keep their IDs
when checked inputs extend the registry. IDs have meaning only in their owning
registry; they are ordinary Core words, never code or heap capabilities.

This module authenticates metadata and reconstructs it. It does not encode
values, generate mapping defaults, evaluate source, or import a source heap.
The strict catalog-backed codec remains a separate representation profile. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreRawMetadata

open TypeSystem SourceInference

/-- The compatibility relation used by the existing public input contract.
Raw nominal arguments and proxy inner types are retained in registry entries. -/
def runtimeType : Ty → Ty
  | .application function argument => .application (runtimeType function) (runtimeType argument)
  | .function parameter result => .function (runtimeType parameter) (runtimeType result)
  | .product left right => .product (runtimeType left) (runtimeType right)
  | .mapping key value => .mapping (runtimeType key) (runtimeType value)
  | .proxy inner => .proxy (runtimeType inner)
  | .comptime inner => runtimeType inner
  | type => type

theorem runtimeType_idempotent (type : Ty) : runtimeType (runtimeType type) = runtimeType type := by
  induction type <;> simp_all [runtimeType]

inductive Metadata where
  | proxy (inner : Ty)
  | mapping (key value : Ty)
  | constructor (instantiation : DataConstructorInstantiation)
  deriving Repr, DecidableEq

def Metadata.type : Metadata → Ty
  | .proxy inner => .proxy inner
  | .mapping key value => .mapping key value
  | .constructor instantiation => instantiation.resultType

private def exactData? (signatures : ProgramSignatures) (id : Resolved.DeclarationId) :
    Option ProgramDataSignature :=
  match signatures.dataTypes.filter (fun signature => decide (signature.id = id)) with
  | [signature] => some signature
  | _ => none

private def exactConstructor? (signature : ProgramDataSignature) (id : ProgramDataConstructorId) :
    Option ProgramDataConstructorSignature :=
  match signature.constructors.filter (fun constructor => decide (constructor.id = id)) with
  | [constructor] => some constructor
  | _ => none

/-- Exact signature reconstruction, including substitution order, payloads,
and result metadata. No catalog tag or self-reported Core type authenticates a
source constructor. Lookup follows the established public validation rule. -/
def constructorAuthentic (signatures : ProgramSignatures)
    (instantiation : DataConstructorInstantiation) : Bool :=
  match exactData? signatures instantiation.constructor.dataType with
  | none => false
  | some signature =>
      match exactConstructor? signature instantiation.constructor with
      | none => false
      | some constructor =>
          if instantiation.parameterSubstitution.map Prod.fst != signature.parameters then false
          else
            match signature.parameters.mapM instantiation.parameterSubstitution.lookup? with
            | none => false
            | some arguments =>
                instantiation.payloadTypes = constructor.payloadTypes.map instantiation.parameterSubstitution.apply &&
                  instantiation.resultType = Ty.nominal signature.id arguments

def Metadata.authentic (signatures : ProgramSignatures) : Metadata → Bool
  | .proxy _ | .mapping _ _ => true
  | .constructor instantiation => constructorAuthentic signatures instantiation

/-- Size limits apply to distinct metadata entries. Word conversion checks
the independent numeric bound even when a caller chooses a larger limit. -/
structure Limits where
  maxEntries : Nat := 65536
  deriving Repr, DecidableEq

inductive Error where
  | runtimeTypeMismatch (expected actual : Ty)
  | invalidConstructor (instantiation : DataConstructorInstantiation)
  | entryBudgetExhausted (maximum : Nat)
  | wordSpaceExhausted
  deriving Repr, DecidableEq

structure Registry where private mk ::
  private signatureValue : ProgramSignatures
  private limitValue : Limits
  private metadataValues : List Metadata
  private staticCount : Nat
  private authenticated : ∀ metadata, metadata ∈ metadataValues → metadata.authentic signatureValue = true
  private unique : metadataValues.Nodup
  private staticBound : staticCount ≤ metadataValues.length

namespace Registry

def signatures (registry : Registry) : ProgramSignatures := registry.signatureValue
def limits (registry : Registry) : Limits := registry.limitValue
def entries (registry : Registry) : List Metadata := registry.metadataValues
def staticLength (registry : Registry) : Nat := registry.staticCount
def length (registry : Registry) : Nat := registry.entries.length

/-- Zero is reserved. A valid ID is the nonwrapping one-based list index. -/
def lookup (registry : Registry) (id : Core.Word) : Option Metadata :=
  if id.val = 0 then none else registry.entries[id.val - 1]?

theorem lookup_zero (registry : Registry) : registry.lookup Core.Word.zero = none := by
  simp [lookup, Core.Word.zero]

theorem entries_authenticated (registry : Registry) (metadata : Metadata)
    (member : metadata ∈ registry.entries) : metadata.authentic registry.signatures = true :=
  registry.authenticated metadata member

theorem entries_unique (registry : Registry) : registry.entries.Nodup := registry.unique

theorem staticLength_le_length (registry : Registry) : registry.staticLength ≤ registry.length :=
  registry.staticBound

theorem lookup_authenticated {registry : Registry} {id : Core.Word} {metadata : Metadata}
    (found : registry.lookup id = some metadata) : metadata.authentic registry.signatures = true := by
  unfold lookup at found
  split at found
  · contradiction
  · exact registry.entries_authenticated metadata (List.mem_of_getElem? found)

end Registry

/-- A suffix extension preserves the signature owner, limit, static prefix,
and all previously issued IDs. There is no public registry editing API. -/
structure Extends (before after : Registry) : Prop where
  signatures : after.signatures = before.signatures
  limits : after.limits = before.limits
  staticLength : after.staticLength = before.staticLength
  suffix : ∃ suffix, after.entries = before.entries ++ suffix

theorem Extends.refl (registry : Registry) : Extends registry registry :=
  ⟨rfl, rfl, rfl, ⟨[], by simp⟩⟩

theorem Extends.lookup {before after : Registry} (extension : Extends before after)
    {id : Core.Word} {metadata : Metadata} (found : before.lookup id = some metadata) :
    after.lookup id = some metadata := by
  obtain ⟨suffix, appended⟩ := extension.suffix
  unfold Registry.lookup at found ⊢
  split at found
  · contradiction
  · rename_i positive
    rw [if_neg positive, appended]
    exact List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1 ▸ found

theorem Extends.trans {first second third : Registry}
    (left : Extends first second) (right : Extends second third) : Extends first third := by
  obtain ⟨leftSuffix, leftAppended⟩ := left.suffix
  obtain ⟨rightSuffix, rightAppended⟩ := right.suffix
  exact ⟨right.signatures.trans left.signatures, right.limits.trans left.limits,
    right.staticLength.trans left.staticLength,
    ⟨leftSuffix ++ rightSuffix, by rw [rightAppended, leftAppended, List.append_assoc]⟩⟩

private def findIndex (values : List Metadata) (metadata : Metadata) :
    Option { index : Nat // values[index]? = some metadata } :=
  match values with
  | [] => none
  | head :: tail =>
      if same : head = metadata then some ⟨0, by simp [same]⟩
      else match findIndex tail metadata with
        | none => none
        | some index => some ⟨index.val + 1, by simpa using index.property⟩

private theorem findIndex_none {values : List Metadata} {metadata : Metadata}
    (absent : findIndex values metadata = none) : metadata ∉ values := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      by_cases same : head = metadata
      · simp [findIndex, same] at absent
      · cases found : findIndex tail metadata with
        | none => simpa [List.mem_cons, Ne.symm same] using ih found
        | some index => simp [findIndex, same, found] at absent

private theorem ofNat_val {number : Nat} {word : Core.Word}
    (converted : Core.Word.ofNat? number = some word) : word.val = number := by
  unfold Core.Word.ofNat? at converted
  split at converted
  · cases converted; rfl
  · contradiction

private theorem lookup_at {registry : Registry} {number : Nat} {word : Core.Word} {metadata : Metadata}
    (converted : Core.Word.ofNat? (number + 1) = some word)
    (found : registry.entries[number]? = some metadata) : registry.lookup word = some metadata := by
  have value := ofNat_val converted
  simp [Registry.lookup, value, found]

/-- The checked one-based encoding is public for numeric budget tests. It
cannot register metadata or confer ownership of another registry's ID. -/
def idAt? (index : Nat) : Option Core.Word := Core.Word.ofNat? (index + 1)

theorem idAt?_value {index : Nat} {id : Core.Word} (found : idAt? index = some id) :
    id.val = index + 1 := ofNat_val found

theorem idAt?_nonzero {index : Nat} {id : Core.Word} (found : idAt? index = some id) :
    id ≠ Core.Word.zero := by
  intro zero
  have value := idAt?_value found
  rw [zero] at value
  simp [Core.Word.zero] at value

/-- Existing entries can be selected without extending the registry. -/
def Registry.id? (registry : Registry) (metadata : Metadata) : Option Core.Word := do
  let index ← findIndex registry.entries metadata
  idAt? index.val

theorem Registry.id?_reconstruct {registry : Registry} {metadata : Metadata} {id : Core.Word}
    (found : registry.id? metadata = some id) : registry.lookup id = some metadata := by
  unfold Registry.id? at found
  cases selected : findIndex registry.entries metadata with
  | none => simp [selected] at found
  | some index =>
      simp only [selected] at found
      exact lookup_at found index.property

structure Inserted (before : Registry) (expected : Ty) (metadata : Metadata) where private mk ::
  private nextRegistry : Registry
  private assignedId : Core.Word
  private reconstructed : nextRegistry.lookup assignedId = some metadata
  private extension : Extends before nextRegistry
  private compatible : runtimeType expected = runtimeType metadata.type

namespace Inserted

def registry {before : Registry} {expected : Ty} {metadata : Metadata} (inserted : Inserted before expected metadata) : Registry :=
  inserted.nextRegistry
def id {before : Registry} {expected : Ty} {metadata : Metadata} (inserted : Inserted before expected metadata) : Core.Word :=
  inserted.assignedId
theorem reconstruct {before : Registry} {expected : Ty} {metadata : Metadata} (inserted : Inserted before expected metadata) :
    inserted.registry.lookup inserted.id = some metadata := inserted.reconstructed
theorem preserves {before : Registry} {expected : Ty} {metadata : Metadata} (inserted : Inserted before expected metadata) :
    Extends before inserted.registry := inserted.extension
theorem runtime_compatible {before : Registry} {expected : Ty} {metadata : Metadata}
    (inserted : Inserted before expected metadata) :
    runtimeType expected = runtimeType metadata.type := inserted.compatible
theorem authenticated {before : Registry} {expected : Ty} {metadata : Metadata}
    (inserted : Inserted before expected metadata) : metadata.authentic before.signatures = true := by
  have valid := Registry.lookup_authenticated inserted.reconstruct
  rw [inserted.preserves.signatures] at valid
  exact valid
theorem nonzero {before : Registry} {expected : Ty} {metadata : Metadata}
    (inserted : Inserted before expected metadata) : inserted.id ≠ Core.Word.zero := by
  intro zero
  have reconstructed := inserted.reconstruct
  rw [zero, Registry.lookup_zero] at reconstructed
  contradiction

end Inserted

/-- Authenticate before interning. Reusing a metadata entry consumes no new
slot. The returned receipt certifies reconstruction and preservation of all
old IDs. Expected type compatibility does not canonicalize raw metadata. -/
def Registry.intern (registry : Registry) (expected : Ty) (metadata : Metadata) :
    Except Error (Inserted registry expected metadata) := do
  if compatible : runtimeType expected = runtimeType metadata.type then
    if authenticated : metadata.authentic registry.signatures = true then
      match found : findIndex registry.entries metadata with
      | some index =>
          match converted : Core.Word.ofNat? (index.val + 1) with
          | none => throw .wordSpaceExhausted
          | some word => pure (.mk registry word (lookup_at converted index.property) (.refl registry) compatible)
      | none =>
          if registry.length ≥ registry.limits.maxEntries then
            throw (.entryBudgetExhausted registry.limits.maxEntries)
          match converted : Core.Word.ofNat? (registry.length + 1) with
          | none => throw .wordSpaceExhausted
          | some word =>
              let next : Registry := .mk registry.signatures registry.limits (registry.entries ++ [metadata])
                registry.staticLength
                (by
                  intro candidate member
                  simp only [List.mem_append, List.mem_singleton] at member
                  rcases member with old | fresh
                  · exact registry.entries_authenticated candidate old
                  · cases fresh; exact authenticated)
                (by
                  apply List.nodup_append.mpr
                  exact ⟨registry.entries_unique, by simp, by
                    intro candidate old fresh freshMember same
                    simp only [List.mem_singleton] at freshMember
                    cases freshMember
                    cases same
                    exact findIndex_none found old⟩)
                (by
                  simpa [Registry.length] using Nat.le_trans registry.staticLength_le_length (Nat.le_add_right registry.length 1))
              have newFound : next.entries[registry.length]? = some metadata := by
                simp [next, Registry.entries, Registry.length]
              pure (.mk next word (lookup_at converted newFound)
                ⟨rfl, rfl, rfl, ⟨[metadata], rfl⟩⟩ compatible)
    else
      by
        cases metadata with
        | constructor instantiation => exact .error (.invalidConstructor instantiation)
        | proxy inner => simp [Metadata.authentic] at authenticated
        | mapping key value => simp [Metadata.authentic] at authenticated
  else
    throw (.runtimeTypeMismatch expected metadata.type)

private def empty (signatures : ProgramSignatures) (limits : Limits) : Registry :=
  .mk signatures limits [] 0 (by simp) (by simp) (by simp)

private def addStatic : (registry : Registry) → List Metadata → Except Error Registry
  | registry, [] => pure registry
  | registry, metadata :: rest => do
      let inserted ← registry.intern metadata.type metadata
      addStatic inserted.registry rest

private theorem addStatic_signatures {before after : Registry} {metadata : List Metadata}
    (accepted : addStatic before metadata = .ok after) : after.signatures = before.signatures := by
  induction metadata generalizing before after with
  | nil => cases accepted; rfl
  | cons head tail ih =>
      simp only [addStatic] at accepted
      cases inserted : before.intern head.type head with
      | error error => simp [inserted, bind, Except.bind] at accepted
      | ok receipt =>
          have continued : addStatic receipt.registry tail = .ok after := by
            simpa [inserted, bind, Except.bind] using accepted
          exact (ih continued).trans receipt.preserves.signatures

/-- Preparation interns static metadata in discovery order, then seals that
prefix. Dynamic input extensions preserve this prefix and its IDs. -/
def prepare (signatures : ProgramSignatures) (staticMetadata : List Metadata)
    (limits : Limits := {}) : Except Error Registry := do
  let registry ← addStatic (empty signatures limits) staticMetadata
  pure (.mk registry.signatures registry.limits registry.entries registry.length
    registry.authenticated registry.unique (Nat.le_refl _))

theorem prepare_signatures {signatures : ProgramSignatures} {metadata : List Metadata}
    {limits : Limits} {registry : Registry}
    (accepted : prepare signatures metadata limits = .ok registry) : registry.signatures = signatures := by
  unfold prepare at accepted
  cases collected : addStatic (empty signatures limits) metadata with
  | error error => simp [collected, bind, Except.bind] at accepted
  | ok prepared =>
      simp only [collected, bind, Except.bind, pure, Except.pure] at accepted
      cases accepted
      exact addStatic_signatures collected

private theorem lookup_same_metadata {values : List Metadata} (unique : values.Nodup)
    {left right : Nat} {metadata : Metadata}
    (leftFound : values[left]? = some metadata) (rightFound : values[right]? = some metadata) : left = right := by
  induction values generalizing left right with
  | nil => simp at leftFound
  | cons head tail ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      cases left <;> cases right
      · rfl
      · simp only [List.getElem?_cons_zero] at leftFound
        cases leftFound
        exact False.elim (absent (List.mem_of_getElem? rightFound))
      · simp only [List.getElem?_cons_zero] at rightFound
        cases rightFound
        exact False.elim (absent (List.mem_of_getElem? leftFound))
      · exact congrArg Nat.succ (ih tailUnique leftFound rightFound)

/-- Comparing authenticated IDs is exactly comparing raw metadata in the same
registry. This is the law consumed by proxy, nominal equality and patterns. -/
theorem Registry.ids_equal_iff {registry : Registry} {left right : Core.Word}
    {leftMetadata rightMetadata : Metadata}
    (leftFound : registry.lookup left = some leftMetadata)
    (rightFound : registry.lookup right = some rightMetadata) :
    left = right ↔ leftMetadata = rightMetadata := by
  constructor
  · intro same; cases same
    exact Option.some.inj (leftFound.symm.trans rightFound)
  · intro same; cases same
    unfold Registry.lookup at leftFound rightFound
    split at leftFound
    · contradiction
    · rename_i leftPositive
      split at rightFound
      · contradiction
      · rename_i rightPositive
        have sameIndex := lookup_same_metadata registry.entries_unique leftFound rightFound
        apply Fin.ext
        omega

theorem Registry.word_equality_iff {registry : Registry} {left right : Core.Word}
    {leftMetadata rightMetadata : Metadata}
    (leftFound : registry.lookup left = some leftMetadata)
    (rightFound : registry.lookup right = some rightMetadata) :
    (left == right) = decide (leftMetadata = rightMetadata) := by
  apply Bool.eq_iff_iff.mpr
  simpa using Registry.ids_equal_iff leftFound rightFound

end Solcore.Frontend.SourceCoreRawMetadata

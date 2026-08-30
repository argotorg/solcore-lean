import Solcore.Abi.StaticWordImplementation
import Solcore.Abi.StaticWordMetadata

/-! Deterministic validation for Static Word ABI method tables. -/

set_option autoImplicit false

namespace Solcore.Abi.V1

/-- Metadata paired with the checked Core implementation it describes. -/
structure Method where
  metadata : MethodMetadata
  implementation : WordImplementation

/-- One method with its canonical signature and selector computed once.
The equality fields prevent the cached dispatch keys from drifting from the
metadata. -/
structure IndexedMethod where
  method : Method
  signature : String
  signature_eq : signature = method.metadata.canonicalSignatureText
  selector : Selector
  selector_eq : selector = method.metadata.selector

namespace Method

def index (method : Method) : IndexedMethod where
  method := method
  signature := method.metadata.canonicalSignatureText
  signature_eq := rfl
  selector := method.metadata.selector
  selector_eq := rfl

end Method

namespace IndexedMethod

/-- Unicode-scalar ordering of canonical ASCII signatures. -/
def signatureLE (left right : IndexedMethod) : Bool :=
  (compare left.signature right.signature).isLE

end IndexedMethod

/-- Index and canonically order methods before selecting any conflict. -/
def canonicalMethodEntries (methods : List Method) : List IndexedMethod :=
  (methods.map Method.index).mergeSort IndexedMethod.signatureLE

/-- The first equal-signature pair in canonical order. -/
def firstDuplicateSignature? :
    List IndexedMethod → Option (IndexedMethod × IndexedMethod)
  | first :: second :: rest =>
      if first.signature == second.signature then
        some (first, second)
      else
        firstDuplicateSignature? (second :: rest)
  | _ => none

/-- The lexicographically first pair sharing a selector. -/
def firstSelectorCollision? :
    List IndexedMethod → Option (IndexedMethod × IndexedMethod)
  | [] => none
  | first :: rest =>
      match rest.find? (fun later => later.selector == first.selector) with
      | some later => some (first, later)
      | none => firstSelectorCollision? rest

/-- A complete and machine-readable method-table validation failure. -/
inductive MethodTableError where
  | empty
  | duplicateSignature
      (first second : MethodMetadata)
      (signature : String)
  | selectorCollision
      (first second : MethodMetadata)
      (firstSignature secondSignature : String)
      (selector : Selector)

/-- A nonempty canonical table whose constructor is available only to this
validator. The retained equations certify both conflict scans. -/
structure MethodTable where
  private mk ::
  entries : List IndexedMethod
  nonempty : entries ≠ []
  noDuplicateSignature : firstDuplicateSignature? entries = none
  noSelectorCollision : firstSelectorCollision? entries = none

namespace MethodTable

/-- Validate every finite input, reporting one canonically selected error. -/
def validate (methods : List Method) : Except MethodTableError MethodTable :=
  match entriesEq : canonicalMethodEntries methods with
  | [] => .error .empty
  | first :: rest =>
      let entries := first :: rest
      match duplicateEq : firstDuplicateSignature? entries with
      | some conflict =>
          .error (.duplicateSignature
            conflict.1.method.metadata
            conflict.2.method.metadata
            conflict.1.signature)
      | none =>
          match collisionEq : firstSelectorCollision? entries with
          | some conflict =>
              .error (.selectorCollision
                conflict.1.method.metadata
                conflict.2.method.metadata
                conflict.1.signature
                conflict.2.signature
                conflict.1.selector)
          | none =>
              .ok {
                entries := entries
                nonempty := by simp [entries]
                noDuplicateSignature := duplicateEq
                noSelectorCollision := collisionEq
              }

end MethodTable

end Solcore.Abi.V1

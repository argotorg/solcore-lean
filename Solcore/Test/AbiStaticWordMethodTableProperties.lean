import Solcore.Abi.StaticWord

/-! External compile consumers for Static Word ABI method-table contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Abi.V1

private theorem compileTimeDuplicateScanComplete
    (entries : List IndexedMethod) :
    firstDuplicateSignature? entries = none ↔
      entries.Pairwise fun left right => left.signature ≠ right.signature :=
  firstDuplicateSignature?_eq_none_iff entries

private theorem compileTimeSelectorScanComplete
    (entries : List IndexedMethod) :
    firstSelectorCollision? entries = none ↔
      entries.Pairwise fun left right => left.selector ≠ right.selector :=
  firstSelectorCollision?_eq_none_iff entries

private theorem compileTimeCanonicalProvenance
    {methods : List Method} {entry : IndexedMethod} :
    entry ∈ canonicalMethodEntries methods ↔
      ∃ method, method ∈ methods ∧ Method.index method = entry :=
  mem_canonicalMethodEntries_iff

private theorem compileTimeCanonicalPermutation (methods : List Method) :
    (canonicalMethodEntries methods).Perm (methods.map Method.index) :=
  canonicalMethodEntries_perm methods

private theorem compileTimeCanonicalSorted (methods : List Method) :
    (canonicalMethodEntries methods).Pairwise fun left right =>
      IndexedMethod.signatureLE left right = true :=
  canonicalMethodEntries_sorted methods

private theorem compileTimeAcceptedProvenance
    {methods : List Method} {table : MethodTable}
    (accepted : MethodTable.validate methods = .ok table)
    {entry : IndexedMethod} (member : entry ∈ table.entries) :
    ∃ method, method ∈ methods ∧ Method.index method = entry :=
  MethodTable.entries_provenance accepted member

private theorem compileTimeAcceptedNonempty (table : MethodTable) :
    table.entries ≠ [] :=
  MethodTable.entries_nonempty table

private theorem compileTimeAcceptedSignatureUnique (table : MethodTable) :
    table.entries.Pairwise fun left right =>
      left.signature ≠ right.signature :=
  MethodTable.signatures_pairwise table

private theorem compileTimeAcceptedSelectorUnique (table : MethodTable) :
    table.entries.Pairwise fun left right => left.selector ≠ right.selector :=
  MethodTable.selectors_pairwise table

private theorem compileTimeAcceptedSorted
    {methods : List Method} {table : MethodTable}
    (accepted : MethodTable.validate methods = .ok table) :
    table.entries.Pairwise fun left right =>
      IndexedMethod.signatureLE left right = true :=
  MethodTable.entries_sorted accepted

private theorem compileTimePermutationPreservesAcceptedEntries
    {firstMethods secondMethods : List Method}
    {firstTable secondTable : MethodTable}
    (permutation : firstMethods.Perm secondMethods)
    (firstAccepted : MethodTable.validate firstMethods = .ok firstTable)
    (secondAccepted : MethodTable.validate secondMethods = .ok secondTable) :
    firstTable.entries = secondTable.entries :=
  MethodTable.entries_eq_of_input_perm permutation
    firstAccepted secondAccepted

private theorem compileTimePermutationPreservesAcceptance
    {firstMethods secondMethods : List Method}
    (permutation : firstMethods.Perm secondMethods) :
    (∃ table, MethodTable.validate firstMethods = .ok table) ↔
      ∃ table, MethodTable.validate secondMethods = .ok table :=
  MethodTable.validate_accepts_iff_of_input_perm permutation

private theorem compileTimePermutationPreservesErrorKind
    {firstMethods secondMethods : List Method}
    {firstError secondError : MethodTableError}
    (permutation : firstMethods.Perm secondMethods)
    (firstRejected : MethodTable.validate firstMethods = .error firstError)
    (secondRejected : MethodTable.validate secondMethods = .error secondError) :
    MethodTable.ErrorKind.ofError firstError =
      MethodTable.ErrorKind.ofError secondError :=
  MethodTable.errorKind_eq_of_input_perm permutation
    firstRejected secondRejected

/-- All checks in this module are elaboration-time proof consumers. -/
def testAbiStaticWordMethodTableProperties : IO Unit :=
  pure ()

end Tests

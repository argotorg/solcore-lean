import Solcore.Surface.Multi.RootlessNormalizationDottedStaticCertificateA19

set_option autoImplicit false
set_option warningAsError true

namespace Solcore.Surface.Multi

open Grammar

private theorem all_drop_split
    {α : Type} (xs : List α) (predicate : α → Bool)
    (start count : Nat) :
    (xs.drop start).all predicate =
      (((xs.drop start).take count).all predicate &&
        (xs.drop (start + count)).all predicate) := by
  calc
    (xs.drop start).all predicate =
        (((xs.drop start).take count) ++
          ((xs.drop start).drop count)).all predicate := by
      rw [List.take_append_drop]
    _ = (((xs.drop start).take count).all predicate &&
          ((xs.drop start).drop count).all predicate) := by
      rw [List.all_append]
    _ = (((xs.drop start).take count).all predicate &&
          (xs.drop (start + count)).all predicate) := by
      rw [List.drop_drop]

private theorem dottedStaticSuffix_true_of_chunk
    (start count : Nat)
    (chunkAccepted : dottedStaticRankChunk start count = true)
    (tailAccepted : (allDottedRhs.zipIdx.drop (start + count)).all
      dottedStaticRankRowAt = true) :
    (allDottedRhs.zipIdx.drop start).all
      dottedStaticRankRowAt = true := by
  unfold dottedStaticRankChunk at chunkAccepted
  rw [all_drop_split allDottedRhs.zipIdx
    dottedStaticRankRowAt start count]
  simp only [chunkAccepted, tailAccepted, Bool.and_self]

/-- Independently checked shards cover the complete fixed static table. -/
theorem dottedStaticRankTable_eq_true :
    dottedStaticRankTable = true := by
  have suffix2368 := dottedStaticRankTail_2368_true
  have suffix2272 := dottedStaticSuffix_true_of_chunk 2272 96
    dottedStaticRankChunk_2272_true suffix2368
  have suffix2176 := dottedStaticSuffix_true_of_chunk 2176 96
    dottedStaticRankChunk_2176_true suffix2272
  have suffix2080 := dottedStaticSuffix_true_of_chunk 2080 96
    dottedStaticRankChunk_2080_true suffix2176
  have suffix1984 := dottedStaticSuffix_true_of_chunk 1984 96
    dottedStaticRankChunk_1984_true suffix2080
  have suffix1888 := dottedStaticSuffix_true_of_chunk 1888 96
    dottedStaticRankChunk_1888_true suffix1984
  have suffix1792 := dottedStaticSuffix_true_of_chunk 1792 96
    dottedStaticRankChunk_1792_true suffix1888
  have suffix1696 := dottedStaticSuffix_true_of_chunk 1696 96
    dottedStaticRankChunk_1696_true suffix1792
  have suffix1600 := dottedStaticSuffix_true_of_chunk 1600 96
    dottedStaticRankChunk_1600_true suffix1696
  have suffix1504 := dottedStaticSuffix_true_of_chunk 1504 96
    dottedStaticRankChunk_1504_true suffix1600
  have suffix1408 := dottedStaticSuffix_true_of_chunk 1408 96
    dottedStaticRankChunk_1408_true suffix1504
  have suffix1312 := dottedStaticSuffix_true_of_chunk 1312 96
    dottedStaticRankChunk_1312_true suffix1408
  have suffix1216 := dottedStaticSuffix_true_of_chunk 1216 96
    dottedStaticRankChunk_1216_true suffix1312
  have suffix1120 := dottedStaticSuffix_true_of_chunk 1120 96
    dottedStaticRankChunk_1120_true suffix1216
  have suffix1024 := dottedStaticSuffix_true_of_chunk 1024 96
    dottedStaticRankChunk_1024_true suffix1120
  have suffix928 := dottedStaticSuffix_true_of_chunk 928 96
    dottedStaticRankChunk_0928_true suffix1024
  have suffix832 := dottedStaticSuffix_true_of_chunk 832 96
    dottedStaticRankChunk_0832_true suffix928
  have suffix736 := dottedStaticSuffix_true_of_chunk 736 96
    dottedStaticRankChunk_0736_true suffix832
  have suffix640 := dottedStaticSuffix_true_of_chunk 640 96
    dottedStaticRankChunk_0640_true suffix736
  have full := dottedStaticSuffix_true_of_chunk 0 640
    dottedStaticRankChunk_0000_true suffix640
  simpa [dottedStaticRankTable] using full

end Solcore.Surface.Multi

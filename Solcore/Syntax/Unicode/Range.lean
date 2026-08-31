namespace Solcore.Syntax.Unicode

/-- Inclusive Unicode scalar-value bounds used by generated category tables. -/
abbrev ScalarRange := Nat × Nat

/-- Test one scalar value against an inclusive range. -/
def ScalarRange.contains (range : ScalarRange) (scalar : Nat) : Bool :=
  range.1 ≤ scalar && scalar ≤ range.2

/-- Fuel-bounded binary search over sorted, disjoint scalar ranges. -/
private def inScalarRangesLoop
    (ranges : Array ScalarRange)
    (scalar lower upper fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
      if lower < upper then
        let middle := lower + (upper - lower) / 2
        match ranges[middle]? with
        | none => false
        | some range =>
            if scalar < range.1 then
              inScalarRangesLoop ranges scalar lower middle fuel
            else if range.2 < scalar then
              inScalarRangesLoop ranges scalar (middle + 1) upper fuel
            else
              true
      else
        false

/-- Test a character against sorted, pairwise-disjoint inclusive scalar ranges. -/
def inScalarRanges (ranges : Array ScalarRange) (character : Char) : Bool :=
  inScalarRangesLoop ranges character.toNat 0 ranges.size (ranges.size + 1)

end Solcore.Syntax.Unicode

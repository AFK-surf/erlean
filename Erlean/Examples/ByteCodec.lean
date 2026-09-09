import Erlean.Examples.ImportedByteCodec
import Erlean.Logic.ObservableContract

namespace Erlean.Examples

open Core Semantics Logic

/-- The actual imported codec normalizes every integer modulo 256. -/
theorem byte_roundtrip_run (value : Int) :
    runLocal 100 [importedByteCodec]
      (initialCall "byte_codec" "roundtrip" [.integer value]) =
      .halted (.returned [.tuple [.atom "ok", .integer (value % 256)]]) := by
  simp [runLocal, run, initialCall, importedByteCodec, stepLocal, startCollect,
    finishCollect, nextControl, invoke, lookupFunction, Env.lookup,
    patternsObservationAllowed, patternObservationAllowed, matchPatterns, matchPattern,
    encodeByteValues, decodeByteValues_single, BEq.beq, List.beq, Value.equal]

theorem byte_roundtrip_totalCorrect :
    TotalCorrect [importedByteCodec] "byte_codec" "roundtrip"
      (fun args => ∃ value : Int, 0 ≤ value ∧ value < 256 ∧ args = [.integer value])
      (fun args result => ∀ value, args = [.integer value] →
        result = .returned [.tuple [.atom "ok", .integer value]]) := by
  apply totalCorrect_of_evaluates
  intro args hp
  obtain ⟨value, nonnegative, bounded, rfl⟩ := hp
  have evaluation := run_halted_sound _ 100 (byte_roundtrip_run value)
  rw [Int.emod_eq_of_lt nonnegative bounded] at evaluation
  refine ⟨_, evaluation, trivial, ?_⟩
  intro other same
  have equal : value = other := by simpa using same
  subst other
  rfl

theorem byte_roundtrip_observableTotalCorrect :
    ObservableTotalCorrect [importedByteCodec] "byte_codec" "roundtrip"
      (fun args => ∃ value : Int, 0 ≤ value ∧ value < 256 ∧ args = [.integer value])
      (fun args result => ∀ value, args = [.integer value] →
        result = .returned [.tuple [.atom "ok", .integer value]]) := by
  apply observableTotalCorrect_of_totalCorrect byte_roundtrip_totalCorrect
  intro args result precondition postcondition
  obtain ⟨value, _, _, same⟩ := precondition
  rw [postcondition value same]
  simp [observeOutcome, Value.publicList, Value.isPublic]

end Erlean.Examples

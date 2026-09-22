import Shogi

/- Run with `lake env lean tests/ProofAudit.lean`.
The public theorem must have no premises and must refer to the real generator.
`#print axioms` also exposes accidental sorryAx or native-decide dependencies.
-/
example (p : Shogi.Position) (m : Shogi.Move) :
    m ∈ Shogi.legalMoves p ↔ Shogi.Spec.LegalMove p m :=
  Shogi.legalMoves_correct p m

#print axioms Shogi.legalMoves_correct
#print axioms Shogi.legalMoves_sound
#print axioms Shogi.legalMoves_complete

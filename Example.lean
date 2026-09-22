import Shogi

-- In VS Code / Lean's InfoView:
#eval Shogi.legalMovesUSI Shogi.startSFEN

-- Expected: Except.ok 30.
#eval (Shogi.legalMovesUSI Shogi.startSFEN).map List.length

-- Captures, drops, and promotions are handled by the same API.
#eval Shogi.legalMovesUSI "4k4/9/9/9/9/9/9/9/4K4 b P 1"

-- A checked transition followed by generation of the opponent's replies.
def after76Pawn : Except String (List String) := do
  let p <- Shogi.parseSFEN Shogi.startSFEN
  let next <- Shogi.playUSI p "7g7f"
  return (Shogi.legalMoves next).map Shogi.Move.toUSI

#eval after76Pawn

/-!
The next example uses the formal correctness theorem for one concrete move.
Square 56 is 7g and square 47 is 7f in the SFEN coordinate convention.
-/

def initialPosition : Shogi.Position :=
  match Shogi.parseSFEN Shogi.startSFEN with
  | .ok p => p
  | .error _ => {}

def pawn76 : Shogi.Move :=
  .normal ⟨56, by decide⟩ ⟨47, by decide⟩ false

/-- The executable generator contains 7g7f in the initial position. -/
theorem pawn76_generated : pawn76 ∈ Shogi.legalMoves initialPosition := by
  native_decide

/-- Soundness turns generated-list membership into the independent rule spec. -/
theorem pawn76_is_legal : Shogi.Spec.LegalMove initialPosition pawn76 :=
  Shogi.legalMoves_sound initialPosition pawn76 pawn76_generated

/-- Completeness turns satisfaction of the rule spec back into generation. -/
example : pawn76 ∈ Shogi.legalMoves initialPosition :=
  Shogi.legalMoves_complete initialPosition pawn76 pawn76_is_legal

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

import Shogi

private def emit (r : Except String String) : IO UInt32 := do
  match r with
  | .ok text =>
    IO.println text
    return 0
  | .error message =>
    let stderr <- IO.getStderr
    stderr.putStrLn s!"error: {message}"
    return 2

private def movesLine (sfen : String) : Except String String := do
  return String.intercalate " " (<- Shogi.legalMovesUSI sfen)

/-- One SFEN per input line, one space-separated move list per output line.
Errors produce an ERROR-prefixed line, without disrupting later requests. -/
private def batch : IO UInt32 := do
  let stdin <- IO.getStdin
  let stdout <- IO.getStdout
  let mut finished := false
  let mut exitCode : UInt32 := 0
  while !finished do
    let line <- stdin.getLine
    if line.isEmpty then
      finished := true
    else
      match movesLine line with
      | .ok text => stdout.putStrLn text
      | .error message =>
        stdout.putStrLn s!"ERROR\t{message}"
        exitCode := 2
      stdout.flush
  return exitCode

private def usage : String :=
  "Usage:\n" ++
  "  shogi '<board> <b|w> <hands|-> <move-number>'\n" ++
  "  shogi --startpos\n" ++
  "  shogi --count '<sfen>'\n" ++
  "  shogi --play '<sfen>' '<usi-move>'\n" ++
  "  shogi --perft <depth> '<sfen>'\n" ++
  "  shogi --batch   # one SFEN per stdin line\n\n" ++
  "Output is a space-separated list of all position-local legal USI moves.\n" ++
  "No repetition adjudication, entering-king declarations, or USI engine loop."

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["--help"] =>
    IO.println usage
    return 0
  | ["--startpos"] => emit (movesLine Shogi.startSFEN)
  | ["--batch"] => batch
  | ["--count", sfen] => emit do
    let moves <- Shogi.legalMovesUSI sfen
    return toString moves.length
  | ["--play", sfen, usi] => emit do
    let p <- Shogi.parseSFEN sfen
    let next <- Shogi.playUSI p usi
    return Shogi.toSFEN next
  | ["--perft", depthText, sfen] => emit do
    let depth <- match depthText.toNat? with
      | none => throw "depth must be a nonnegative integer"
      | some n => pure n
    let p <- Shogi.parseSFEN sfen
    return toString (Shogi.perft p depth)
  | _ => emit (movesLine (String.intercalate " " args))

import Std
import Init.Data.List.FinRange
import Init.Data.Vector.Basic

/-!
# SFEN -> legal USI moves

A pure Lean 4 reference implementation. No FFI, mathlib, or external engine.
Only position-local legality is considered; repetition requires game history.

Coordinates follow SFEN order: index 0 = 9a, index 80 = 1i.
Use `parseSFEN` or `legalMovesUSI` at the untrusted-input boundary.
`Position` values constructed by hand should pass `validatePosition` first.
-/
namespace Shogi

inductive Color where
  | black | white
  deriving BEq, DecidableEq, Repr, ReflBEq, LawfulBEq

def Color.other : Color -> Color
  | .black => .white
  | .white => .black

inductive Kind where
  | pawn | lance | knight | silver | gold | bishop | rook | king
  deriving BEq, DecidableEq, Repr, ReflBEq, LawfulBEq

def Kind.canPromote : Kind -> Bool
  | .gold | .king => false
  | _ => true

def Kind.letter : Kind -> Char
  | .pawn => 'P'
  | .lance => 'L'
  | .knight => 'N'
  | .silver => 'S'
  | .gold => 'G'
  | .bishop => 'B'
  | .rook => 'R'
  | .king => 'K'

def Kind.handIndex : Kind -> Option (Fin 7)
  | .pawn => some 0
  | .lance => some 1
  | .knight => some 2
  | .silver => some 3
  | .gold => some 4
  | .bishop => some 5
  | .rook => some 6
  | .king => none

def handKinds : List Kind :=
  [.pawn, .lance, .knight, .silver, .gold, .bishop, .rook]

structure Piece where
  color : Color
  kind : Kind
  promoted : Bool := false
  deriving BEq, DecidableEq, Repr, ReflBEq, LawfulBEq

abbrev Square := Fin 81
abbrev Board := Vector (Option Piece) 81
abbrev Hand := Vector Nat 7

def squares : List Square := List.finRange 81

def row (s : Square) : Nat := s.val / 9

def col (s : Square) : Nat := s.val % 9

/-- Bounds-checked construction. Negative integers are never truncated to zero. -/
def squareAt (r c : Int) : Option Square :=
  if r < 0 then none
  else if 9 <= r then none
  else if c < 0 then none
  else if 9 <= c then none
  else
    let i := r.toNat * 9 + c.toNat
    if h : i < 81 then some (Fin.mk i h) else none

def squareUSI (s : Square) : String :=
  String.ofList [Char.ofNat (48 + (9 - col s)), Char.ofNat (97 + row s)]

private def put (b : Board) (s : Square) (p : Option Piece) : Board :=
  b.set s.val p s.isLt

structure Hands where
  black : Hand := Vector.replicate 7 0
  white : Hand := Vector.replicate 7 0
  deriving Repr

def Hands.forColor (h : Hands) : Color -> Hand
  | .black => h.black
  | .white => h.white

def Hands.count (h : Hands) (c : Color) (k : Kind) : Nat :=
  match k.handIndex with
  | none => 0
  | some i => (h.forColor c).get i

def Hands.setCount (h : Hands) (c : Color) (k : Kind) (n : Nat) : Hands :=
  match k.handIndex with
  | none => h
  | some i =>
    let a := (h.forColor c).set i.val n i.isLt
    match c with
    | .black => { h with black := a }
    | .white => { h with white := a }

structure Position where
  board : Board := Vector.replicate 81 none
  turn : Color := .black
  hands : Hands := {}
  moveNumber : Nat := 1
  deriving Repr

inductive Move where
  | normal (src dst : Square) (promote : Bool)
  | drop (kind : Kind) (dst : Square)
  deriving BEq, DecidableEq, Repr, ReflBEq, LawfulBEq

def Move.toUSI : Move -> String
  | .normal src dst promote =>
    squareUSI src ++ squareUSI dst ++ (if promote then "+" else "")
  | .drop kind dst => String.singleton kind.letter ++ "*" ++ squareUSI dst

private def sign (n : Int) : Int :=
  if n < 0 then -1 else if n == 0 then 0 else 1

/-- Only called for horizontal, vertical, or diagonal slider motion. -/
private def clearPath (b : Board) (src dst : Square) : Bool :=
  let dr : Int := (row dst : Int) - (row src : Int)
  let dc : Int := (col dst : Int) - (col src : Int)
  let steps := max dr.natAbs dc.natAbs
  ((List.range steps).drop 1).all fun i =>
    match squareAt ((row src : Int) + sign dr * (i : Int))
                   ((col src : Int) + sign dc * (i : Int)) with
    | none => false
    | some s => (b.get s).isNone

/-- Geometric attacks, including attacks by pinned pieces. Destination occupancy
is deliberately not checked here. Used for king safety and move generation. -/
def attacks (b : Board) (p : Piece) (src dst : Square) : Bool :=
  if src == dst then false else
  let dr : Int := (row dst : Int) - (row src : Int)
  let dc : Int := (col dst : Int) - (col src : Int)
  let forward : Int := if p.color == .black then -dr else dr
  let a := dc.natAbs
  let kingStep := decide (a <= 1) && decide (dr.natAbs <= 1)
  let goldStep :=
    (forward == 1 && decide (a <= 1)) ||
    (forward == 0 && a == 1) || (forward == -1 && dc == 0)
  match p.kind with
  | .pawn => if p.promoted then goldStep else dc == 0 && forward == 1
  | .lance =>
    if p.promoted then goldStep
    else dc == 0 && decide (0 < forward) && clearPath b src dst
  | .knight => if p.promoted then goldStep else a == 1 && forward == 2
  | .silver =>
    if p.promoted then goldStep
    else (forward == 1 && decide (a <= 1)) || (forward == -1 && a == 1)
  | .gold => goldStep
  | .bishop =>
    (a == dr.natAbs && clearPath b src dst) || (p.promoted && kingStep)
  | .rook =>
    ((dc == 0 || dr == 0) && clearPath b src dst) || (p.promoted && kingStep)
  | .king => kingStep

def kingSquare (p : Position) (c : Color) : Option Square :=
  squares.find? fun s =>
    match p.board.get s with
    | some q => q.color == c && q.kind == .king
    | none => false

def inCheck (p : Position) (c : Color) : Bool :=
  match kingSquare p c with
  | none => true
  | some king => squares.any fun src =>
    match p.board.get src with
    | some q => q.color != c && attacks p.board q src king
    | none => false

private def inZone (c : Color) (s : Square) : Bool :=
  if c == .black then decide (row s <= 2) else decide (6 <= row s)

/-- Squares on which an unpromoted pawn, lance, or knight has no future move. -/
def deadRank (c : Color) (k : Kind) (s : Square) : Bool :=
  let distance := if c == .black then row s else 8 - row s
  match k with
  | .pawn | .lance => distance == 0
  | .knight => decide (distance <= 1)
  | _ => false

private def hasPawnOnFile (p : Position) (c : Color) (file : Nat) : Bool :=
  squares.any fun s =>
    col s == file &&
    match p.board.get s with
    | some q => q.color == c && q.kind == .pawn && !q.promoted
    | none => false

private def targetAvailable (p : Position) (dst : Square) : Bool :=
  match p.board.get dst with
  | none => true
  | some q => q.color != p.turn && q.kind != .king

/-- Board moves respecting movement, occupancy, and promotion. King safety is
checked later. All legal non-promotions are retained, even when strategically bad. -/
def boardMoves (p : Position) : List Move :=
  squares.flatMap fun src =>
    match p.board.get src with
    | none => []
    | some q =>
      if q.color == p.turn then
        squares.flatMap fun dst =>
          if targetAvailable p dst && attacks p.board q src dst then
            (if q.promoted || !(deadRank q.color q.kind dst) then
              [Move.normal src dst false] else []) ++
            (if !q.promoted && q.kind.canPromote &&
               (inZone q.color src || inZone q.color dst) then
              [Move.normal src dst true] else [])
          else []
      else []

/-- Drops before king-safety and pawn-drop-mate filtering. -/
def dropMoves (p : Position) : List Move :=
  handKinds.flatMap fun k =>
    if 0 < p.hands.count p.turn k then
      (squares.filter fun dst =>
        (p.board.get dst).isNone && !(deadRank p.turn k dst) &&
           !(k == .pawn && hasPawnOnFile p p.turn (col dst))).map (Move.drop k)
    else []

/-- Internal transition: caller must supply a pseudo-legal move. This is NOT a
validation API. Captures demote the captured piece before adding it to the hand. -/
def applyUnchecked (p : Position) (m : Move) : Position :=
  match m with
  | .normal src dst promote =>
    match p.board.get src with
    | none => p
    | some q =>
      let hands := match p.board.get dst with
        | none => p.hands
        | some captured =>
          p.hands.setCount p.turn captured.kind (p.hands.count p.turn captured.kind + 1)
      let moved := { q with promoted := q.promoted || promote }
      { p with
        board := put (put p.board src none) dst (some moved)
        hands := hands
        turn := p.turn.other
        moveNumber := p.moveNumber + 1 }
  | .drop kind dst =>
    { p with
      board := put p.board dst (some { color := p.turn, kind := kind })
      hands := p.hands.setCount p.turn kind (p.hands.count p.turn kind - 1)
      turn := p.turn.other
      moveNumber := p.moveNumber + 1 }

private def kingSafeAfter (p : Position) (m : Move) : Bool :=
  !(inCheck (applyUnchecked p m) p.turn)

/-- `next` is the position after a king-safe pseudo-legal move by `mover`.
A checking dropped pawn attacks the king from an adjacent square. Its check
cannot be blocked by a drop; all possible evasions are therefore board moves.
This avoids both recursive legality checks and an arbitrary search-depth cutoff. -/
def pawnDropMate (mover : Color) (m : Move) (next : Position) : Bool :=
  match m with
  | .drop .pawn dst =>
    match kingSquare next mover.other with
    | none => false
    | some king =>
      let pawn : Piece := { color := mover, kind := .pawn }
      attacks next.board pawn dst king &&
        !((boardMoves next).any (kingSafeAfter next))
  | _ => false

/-- Position-local legal moves. Precondition: the position is structurally valid. -/
def legalMoves (p : Position) : List Move :=
  (boardMoves p ++ dropMoves p).filter fun m =>
    let next := applyUnchecked p m
    !(inCheck next p.turn) && !(pawnDropMate p.turn m next)

/-! ## Declarative position-local rules

The specification below never calls a move generator or a Boolean legality
checker. Coordinates, board access, king lookup and the state transition are
shared data semantics. In particular, pawn-drop replies are quantified moves,
not membership in `boardMoves`. On valid positions each king lookup is unique.
History-dependent rules are outside this specification.
-/
namespace Spec

/-- Every strictly intermediate square of a sliding move is empty. -/
def ClearPath (b : Board) (src dst : Square) : Prop :=
  let dr : Int := (row dst : Int) - (row src : Int)
  let dc : Int := (col dst : Int) - (col src : Int)
  ∀ i : Nat, 0 < i → i < max dr.natAbs dc.natAbs →
    ∃ s, squareAt ((row src : Int) + sign dr * (i : Int))
                  ((col src : Int) + sign dc * (i : Int)) = some s ∧ b.get s = none

def Attacks (b : Board) (p : Piece) (src dst : Square) : Prop :=
  let dr : Int := (row dst : Int) - (row src : Int)
  let dc : Int := (col dst : Int) - (col src : Int)
  let forward : Int := if p.color = .black then -dr else dr
  let a := dc.natAbs
  let kingStep := a ≤ 1 ∧ dr.natAbs ≤ 1
  let goldStep := (forward = 1 ∧ a ≤ 1) ∨
    (forward = 0 ∧ a = 1) ∨ (forward = -1 ∧ dc = 0)
  src ≠ dst ∧ match p.kind with
  | .pawn => if p.promoted then goldStep else dc = 0 ∧ forward = 1
  | .lance => if p.promoted then goldStep
             else dc = 0 ∧ 0 < forward ∧ ClearPath b src dst
  | .knight => if p.promoted then goldStep else a = 1 ∧ forward = 2
  | .silver => if p.promoted then goldStep
              else (forward = 1 ∧ a ≤ 1) ∨ (forward = -1 ∧ a = 1)
  | .gold => goldStep
  | .bishop => (a = dr.natAbs ∧ ClearPath b src dst) ∨
                (p.promoted = true ∧ kingStep)
  | .rook => ((dc = 0 ∨ dr = 0) ∧ ClearPath b src dst) ∨
                (p.promoted = true ∧ kingStep)
  | .king => kingStep

def InZone (c : Color) (s : Square) : Prop :=
  if c = .black then row s ≤ 2 else 6 ≤ row s

def DeadRank (c : Color) (k : Kind) (s : Square) : Prop :=
  let distance := if c = .black then row s else 8 - row s
  match k with
  | .pawn | .lance => distance = 0
  | .knight => distance ≤ 1
  | _ => False

def HasPawnOnFile (p : Position) (c : Color) (file : Nat) : Prop :=
  ∃ s q, col s = file ∧ p.board.get s = some q ∧
    q.color = c ∧ q.kind = .pawn ∧ q.promoted = false

def TargetAvailable (p : Position) (dst : Square) : Prop :=
  ∀ q, p.board.get dst = some q → q.color ≠ p.turn ∧ q.kind ≠ .king

def PromotionAllowed (q : Piece) (src dst : Square) (promote : Bool) : Prop :=
  if promote then
    q.promoted = false ∧ q.kind ≠ .gold ∧ q.kind ≠ .king ∧
      (InZone q.color src ∨ InZone q.color dst)
  else q.promoted = true ∨ ¬DeadRank q.color q.kind dst

def BoardMove (p : Position) : Move → Prop
  | .normal src dst promote =>
    ∃ q, p.board.get src = some q ∧ q.color = p.turn ∧
      TargetAvailable p dst ∧ Attacks p.board q src dst ∧
      PromotionAllowed q src dst promote
  | .drop .. => False

def DropMove (p : Position) : Move → Prop
  | .drop k dst => k ≠ .king ∧ 0 < p.hands.count p.turn k ∧
    p.board.get dst = none ∧ ¬DeadRank p.turn k dst ∧
    ¬(k = .pawn ∧ HasPawnOnFile p p.turn (col dst))
  | .normal .. => False

/-- A missing king is unsafe, matching the public API's defensive convention. -/
def KingSafe (p : Position) (c : Color) : Prop :=
  ∃ king, kingSquare p c = some king ∧
    ∀ src q, p.board.get src = some q → q.color ≠ c →
      ¬Attacks p.board q src king

def PawnDropMate (mover : Color) (m : Move) (next : Position) : Prop :=
  match m with
  | .drop .pawn dst =>
    (∃ king, kingSquare next mover.other = some king ∧
      Attacks next.board { color := mover, kind := .pawn } dst king) ∧
    ¬∃ reply, BoardMove next reply ∧ KingSafe (applyUnchecked next reply) next.turn
  | _ => False

/-- Legal under the position-local rules, including the adjacent pawn check
evasion rule. This is independent of enumeration and Boolean rule checkers. -/
def LegalMove (p : Position) (m : Move) : Prop :=
  (BoardMove p m ∨ DropMove p m) ∧
  KingSafe (applyUnchecked p m) p.turn ∧
  ¬PawnDropMate p.turn m (applyUnchecked p m)

end Spec

/-! ## Reflection and exhaustive-enumeration proofs -/

@[simp] theorem mem_squares (s : Square) : s ∈ squares := List.mem_finRange s

theorem clearPath_correct (b : Board) (src dst : Square) :
    clearPath b src dst = true ↔ Spec.ClearPath b src dst := by
  simp only [clearPath, Spec.ClearPath, List.all_eq_true]
  have range_mem (n i : Nat) : i ∈ (List.range n).drop 1 ↔ 0 < i ∧ i < n := by
    simp only [List.range_eq_range', List.drop_range', List.mem_range'_1]
    omega
  simp only [range_mem, and_imp]
  apply forall_congr'; intro i
  apply forall_congr'; intro _
  apply forall_congr'; intro _
  split <;> simp_all

theorem attacks_correct (b : Board) (q : Piece) (src dst : Square) :
    attacks b q src dst = true ↔ Spec.Attacks b q src dst := by
  cases q with | mk c k promoted =>
    cases c <;> cases k <;> cases promoted <;>
      simp [attacks, Spec.Attacks, clearPath_correct, and_assoc, or_assoc]

theorem deadRank_correct (c : Color) (k : Kind) (s : Square) :
    deadRank c k s = true ↔ Spec.DeadRank c k s := by
  cases c <;> cases k <;> simp [deadRank, Spec.DeadRank]

theorem inZone_correct (c : Color) (s : Square) :
    inZone c s = true ↔ Spec.InZone c s := by
  cases c <;> simp [inZone, Spec.InZone]

theorem hasPawnOnFile_correct (p : Position) (c : Color) (file : Nat) :
    hasPawnOnFile p c file = true ↔ Spec.HasPawnOnFile p c file := by
  simp only [hasPawnOnFile, List.any_eq_true, mem_squares, true_and,
    Bool.and_eq_true, beq_iff_eq, Spec.HasPawnOnFile]
  apply exists_congr; intro s
  cases h : p.board.get s <;> simp [and_assoc]

theorem targetAvailable_correct (p : Position) (dst : Square) :
    targetAvailable p dst = true ↔ Spec.TargetAvailable p dst := by
  cases h : p.board.get dst <;> simp [targetAvailable, Spec.TargetAvailable, h]

theorem promotion_correct (q : Piece) (src dst : Square) :
    (!q.promoted && q.kind.canPromote && (inZone q.color src || inZone q.color dst)) = true ↔
      Spec.PromotionAllowed q src dst true := by
  cases hk : q.kind <;>
    simp [Kind.canPromote, Spec.PromotionAllowed, inZone_correct, hk]

theorem deadRank_false (c : Color) (k : Kind) (s : Square) :
    deadRank c k s = false ↔ ¬Spec.DeadRank c k s := by
  rw [Bool.eq_false_iff, ne_eq, deadRank_correct]

theorem hasPawnOnFile_false (p : Position) (c : Color) (file : Nat) :
    hasPawnOnFile p c file = false ↔ ¬Spec.HasPawnOnFile p c file := by
  rw [Bool.eq_false_iff, ne_eq, hasPawnOnFile_correct]

theorem nonpromotion_correct (q : Piece) (src dst : Square) :
    (q.promoted || !deadRank q.color q.kind dst) = true ↔
      Spec.PromotionAllowed q src dst false := by
  simp [Spec.PromotionAllowed, deadRank_false]

theorem boardMoves_correct (p : Position) (m : Move) :
    m ∈ boardMoves p ↔ Spec.BoardMove p m := by
  simp only [boardMoves, List.mem_flatMap, mem_squares, true_and]
  have source (src : Square) :
      (m ∈ (match p.board.get src with
        | none => []
        | some q => if q.color == p.turn then
            squares.flatMap (fun dst =>
              if targetAvailable p dst && attacks p.board q src dst then
                (if q.promoted || !deadRank q.color q.kind dst then
                  [Move.normal src dst false] else []) ++
                (if !q.promoted && q.kind.canPromote &&
                  (inZone q.color src || inZone q.color dst) then
                  [Move.normal src dst true] else [])
              else [])
          else [])) ↔
      ∃ q dst promote, p.board.get src = some q ∧ q.color = p.turn ∧
        Spec.TargetAvailable p dst ∧ Spec.Attacks p.board q src dst ∧
        Spec.PromotionAllowed q src dst promote ∧ m = .normal src dst promote := by
    cases h : p.board.get src with
    | none => simp
    | some q =>
      simp only [Option.some.injEq]
      by_cases hc : q.color = p.turn
      · have hc' : (q.color == p.turn) = true := by simpa using hc
        rw [ite_eq_left hc']
        simp only [List.mem_flatMap, mem_squares, true_and, List.mem_ite_nil_right,
          List.mem_append, List.mem_singleton, promotion_correct]
        simp only [Bool.and_eq_true, targetAvailable_correct, attacks_correct,
          Bool.exists_bool]
        simp [Spec.PromotionAllowed, deadRank_false]
        grind
      · simp [hc]
  simp only [source]
  cases m <;> simp [Spec.BoardMove] <;> grind

theorem dropMoves_correct (p : Position) (m : Move) :
    m ∈ dropMoves p ↔ Spec.DropMove p m := by
  have kinds (k : Kind) : k ∈ handKinds ↔ k ≠ .king := by
    cases k <;> simp [handKinds]
  simp only [dropMoves, List.mem_flatMap]
  simp [List.mem_map, List.mem_filter, kinds,
    deadRank_false, hasPawnOnFile_false]
  cases m <;> simp [Spec.DropMove] <;> grind

theorem kingSafe_correct (p : Position) (c : Color) :
    inCheck p c = false ↔ Spec.KingSafe p c := by
  unfold inCheck Spec.KingSafe
  cases hk : kingSquare p c with
  | none => simp
  | some king =>
    simp only [Option.some.injEq, List.any_eq_false, mem_squares, true_implies]
    simp only [exists_eq_left']
    apply forall_congr'; intro src
    cases hs : p.board.get src <;> simp [attacks_correct]

theorem pawnDropMate_correct (mover : Color) (m : Move) (next : Position) :
    pawnDropMate mover m next = true ↔ Spec.PawnDropMate mover m next := by
  have replies : (boardMoves next).any (kingSafeAfter next) = true ↔
      ∃ reply, Spec.BoardMove next reply ∧
        Spec.KingSafe (applyUnchecked next reply) next.turn := by
    simp [List.any_eq_true, boardMoves_correct, kingSafeAfter, kingSafe_correct]
  cases m with
  | normal src dst promote => simp [pawnDropMate, Spec.PawnDropMate]
  | drop k dst =>
    cases k <;> simp [pawnDropMate, Spec.PawnDropMate]
    cases hk : kingSquare next mover.other <;>
      simp [attacks_correct, Bool.eq_false_iff, replies]

/-- Soundness and completeness of the actual public generator. -/
theorem legalMoves_correct (p : Position) (m : Move) :
    m ∈ legalMoves p ↔ Spec.LegalMove p m := by
  have mate_false : pawnDropMate p.turn m (applyUnchecked p m) = false ↔
      ¬Spec.PawnDropMate p.turn m (applyUnchecked p m) := by
    rw [Bool.eq_false_iff, ne_eq, pawnDropMate_correct]
  simp [legalMoves, List.mem_filter, List.mem_append, boardMoves_correct,
    dropMoves_correct, kingSafe_correct, mate_false, Spec.LegalMove, or_and_right]

/-- Every generated move satisfies the independent rules. -/
theorem legalMoves_sound (p : Position) (m : Move) :
    m ∈ legalMoves p → Spec.LegalMove p m := (legalMoves_correct p m).mp

/-- Every move satisfying the independent rules is generated. -/
theorem legalMoves_complete (p : Position) (m : Move) :
    Spec.LegalMove p m → m ∈ legalMoves p := (legalMoves_correct p m).mpr

/-- Checked application for moves from external callers. -/
def play (p : Position) (m : Move) : Except String Position :=
  if (legalMoves p).contains m then .ok (applyUnchecked p m)
  else .error s!"illegal move: {m.toUSI}"

/-- Parse and apply a USI move by matching the generated legal moves. -/
def playUSI (p : Position) (usi : String) : Except String Position :=
  match (legalMoves p).find? (fun m => m.toUSI == usi) with
  | none => .error s!"illegal or malformed USI move: {usi}"
  | some m => .ok (applyUnchecked p m)

private def decodeKind (c : Char) : Option Kind :=
  match c with
  | 'P' | 'p' => some .pawn
  | 'L' | 'l' => some .lance
  | 'N' | 'n' => some .knight
  | 'S' | 's' => some .silver
  | 'G' | 'g' => some .gold
  | 'B' | 'b' => some .bishop
  | 'R' | 'r' => some .rook
  | 'K' | 'k' => some .king
  | _ => none

private def decodePiece (c : Char) : Except String Piece :=
  match decodeKind c with
  | none => .error s!"invalid SFEN piece: {c}"
  | some k => .ok { color := if c.isUpper then .black else .white, kind := k }

private def digitValue (c : Char) : Option Nat :=
  if 48 <= c.toNat then
    if c.toNat <= 57 then some (c.toNat - 48) else none
  else none

private def parseBoard (text : String) : Except String Board := do
  let ranks := text.splitOn "/"
  if ranks.length != 9 then throw "SFEN board must have exactly 9 ranks"
  let mut board : Board := Vector.replicate 81 none
  for (r, rankText) in (List.range 9).zip ranks do
    let mut c := 0
    let mut promoted := false
    let mut previousDigit := false
    for ch in rankText.toList do
      if ch == '+' then
        if promoted then throw "repeated promotion marker in SFEN board"
        promoted := true
        previousDigit := false
      else
        match digitValue ch with
        | some n =>
          if promoted then throw "promotion marker must precede a piece"
          if n == 0 then throw "zero is not a valid SFEN empty-square run"
          if previousDigit then throw "adjacent empty-square digits in SFEN rank"
          if 9 < c + n then throw s!"SFEN rank {r + 1} is wider than 9 squares"
          c := c + n
          previousDigit := true
        | none =>
          let q <- decodePiece ch
          if promoted && !q.kind.canPromote then
            throw "a king or gold cannot be promoted"
          if 9 <= c then throw s!"too many squares in SFEN rank {r + 1}"
          let i := r * 9 + c
          if h : i < 81 then
            board := put board (Fin.mk i h) (some { q with promoted := promoted })
          else
            throw "SFEN square outside the board"
          c := c + 1
          promoted := false
          previousDigit := false
    if promoted then throw "dangling promotion marker at end of SFEN rank"
    if c != 9 then throw s!"SFEN rank {r + 1} must describe exactly 9 squares"
  return board

private def parseHands (text : String) : Except String Hands := do
  if text == "-" then return {}
  if text.isEmpty then throw "empty SFEN hand field; use - for no hands"
  let mut hands : Hands := {}
  let mut count := 0
  let mut hasCount := false
  for ch in text.toList do
    match digitValue ch with
    | some n =>
      if !hasCount && n == 0 then throw "hand counts cannot start with zero"
      count := count * 10 + n
      if 18 < count then throw "hand count exceeds the standard shogi inventory"
      hasCount := true
    | none =>
      let q <- decodePiece ch
      if q.kind == .king then throw "a king cannot be in hand"
      if hands.count q.color q.kind != 0 then
        throw "a hand piece type occurs more than once for the same player"
      let n := if hasCount then count else 1
      hands := hands.setCount q.color q.kind n
      count := 0
      hasCount := false
  if hasCount then throw "hand count is missing its piece letter"
  return hands

private def words (s : String) : List String :=
  let normalized := String.ofList (s.toList.map fun c =>
    if c == '\t' || c == '\n' || c == '\r' then ' ' else c)
  (normalized.splitOn " ").filter (fun w => !w.isEmpty)

private def maxInventory : Kind -> Nat
  | .pawn => 18
  | .lance | .knight | .silver | .gold => 4
  | .bishop | .rook | .king => 2

/-- Sanity checks, not a proof of historical reachability.
Both kings must be present. Missing non-king material is allowed (handicaps and
composed positions), but excess material, dead pieces, and nifu are rejected.
The non-moving player cannot already be in check in a legal input position. -/
def validatePosition (p : Position) : Except String Unit := do
  if p.moveNumber == 0 then throw "SFEN move number must be positive"
  for c in ([.black, .white] : List Color) do
    let kings := squares.filter fun s =>
      match p.board.get s with
      | some q => q.color == c && q.kind == .king
      | none => false
    if kings.length != 1 then throw "exactly one king per side is required"
    for f in List.range 9 do
      let pawns := squares.filter fun s =>
        col s == f &&
        match p.board.get s with
        | some q => q.color == c && q.kind == .pawn && !q.promoted
        | none => false
      if 1 < pawns.length then throw "input position already contains nifu"
  for s in squares do
    match p.board.get s with
    | none => pure ()
    | some q =>
      if q.promoted && !q.kind.canPromote then throw "invalid promoted piece"
      if !q.promoted && deadRank q.color q.kind s then
        throw "input contains an unpromoted piece on a dead rank"
  for k in handKinds ++ [.king] do
    let onBoard := (squares.filter fun s =>
      match p.board.get s with
      | some q => q.kind == k
      | none => false).length
    let total := onBoard + p.hands.count .black k + p.hands.count .white k
    if maxInventory k < total then throw s!"too many {k.letter} pieces in position"
  if inCheck p p.turn.other then
    throw "the non-moving player's king is already in check"

/-- Parse the four SFEN fields. Accepts spaces, tabs, CR, and LF as separators.
Does not accept a `position sfen` prefix or a trailing `moves` clause. -/
def parseSFEN (sfen : String) : Except String Position := do
  if 4096 < sfen.utf8ByteSize then throw "SFEN input exceeds 4096 bytes"
  match words sfen with
  | [boardText, turnText, handText, numberText] =>
    let board <- parseBoard boardText
    let turn <- match turnText with
      | "b" => pure Color.black
      | "w" => pure Color.white
      | _ => throw "SFEN turn must be b or w"
    let hands <- parseHands handText
    let number <- match numberText.toNat? with
      | some n => pure n
      | none => throw "invalid SFEN move number"
    let p : Position :=
      { board := board, turn := turn, hands := hands, moveNumber := number }
    validatePosition p
    return p
  | _ => throw "expected four SFEN fields: <board> <b|w> <hands|-> <move-number>"

/-- Main external API: validated SFEN -> every position-local legal USI move. -/
def legalMovesUSI (sfen : String) : Except String (List String) := do
  let p <- parseSFEN sfen
  return (legalMoves p).map Move.toUSI

/-- Canonical SFEN output, useful after `playUSI` and for round-trip tests. -/
def toSFEN (p : Position) : String := Id.run do
  let mut ranks : List String := []
  for r in List.range 9 do
    let mut text := ""
    let mut empty := 0
    for c in List.range 9 do
      match p.board.getD (r * 9 + c) none with
      | none => empty := empty + 1
      | some q =>
        if 0 < empty then text := text ++ toString empty
        empty := 0
        let letter := if q.color == .black then q.kind.letter else q.kind.letter.toLower
        text := text ++ (if q.promoted then "+" else "") ++ String.singleton letter
    if 0 < empty then text := text ++ toString empty
    ranks := text :: ranks
  let mut hands := ""
  for c in ([.black, .white] : List Color) do
    for k in handKinds.reverse do
      let n := p.hands.count c k
      if 0 < n then
        if 1 < n then hands := hands ++ toString n
        let letter := if c == .black then k.letter else k.letter.toLower
        hands := hands ++ String.singleton letter
  if hands.isEmpty then hands := "-"
  let turn := if p.turn == .black then "b" else "w"
  return String.intercalate "/" ranks.reverse ++ " " ++ turn ++ " " ++ hands ++
    " " ++ toString p.moveNumber

/-- Exhaustive node count, primarily a test helper, not an optimized search. -/
def perft (p : Position) : Nat -> Nat
  | 0 => 1
  | depth + 1 =>
    (legalMoves p).foldl (fun n m => n + perft (applyUnchecked p m) depth) 0

def startSFEN : String :=
  "lnsgkgsnl/1r5b1/ppppppppp/9/9/9/PPPPPPPPP/1B5R1/LNSGKGSNL b - 1"

end Shogi

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

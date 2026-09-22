"""Independent ray-based Python sanity model; NOT a Lean compiler or proof."""
from dataclasses import dataclass

START = 'lnsgkgsnl/1r5b1/ppppppppp/9/9/9/PPPPPPPPP/1B5R1/LNSGKGSNL b - 1'

def sq(s):
    return (ord(s[1])-97)*9+9-int(s[0])
def usq(s):
    return str(9-s%9)+chr(97+s//9)
def make(mapping, hands='-', turn='b', number=1):
    rows=[]
    for r in range(9):
        text=''; n=0
        for c in range(9):
            q=mapping.get(usq(r*9+c))
            if q:
                if n: text+=str(n); n=0
                text+=q
            else: n+=1
        if n: text+=str(n)
        rows.append(text)
    return '/'.join(rows)+f' {turn} {hands} {number}'

@dataclass
class Pos:
    board: list
    turn: int
    hands: list
    number: int

def parse(s):
    layout, turn, ht, number=s.split()
    board=[]
    for rank in layout.split('/'):
        pro=False
        for c in rank:
            if c=='+': pro=True
            elif c.isdigit(): board.extend([None]*int(c))
            else:
                board.append((0 if c.isupper() else 1,c.upper(),pro)); pro=False
    hands=[{},{}]; n=''
    if ht!='-':
        for c in ht:
            if c.isdigit(): n+=c
            else: hands[int(c.islower())][c.upper()]=int(n or '1'); n=''
    return Pos(board,int(turn=='w'),hands,int(number))

def targets(p, src):
    color,k,prom=p.board[src]; f=-1 if color==0 else 1
    gold=[(f,-1),(f,0),(f,1),(0,-1),(0,1),(-f,0)]
    king=[(r,c) for r in [-1,0,1] for c in [-1,0,1] if r or c]
    diag=[(-1,-1),(-1,1),(1,-1),(1,1)]
    orth=[(-1,0),(1,0),(0,-1),(0,1)]
    ray=[]; step=[]
    if k=='K': step=king
    elif k=='G' or (prom and k in 'PLNS'): step=gold
    elif k=='P': step=[(f,0)]
    elif k=='N': step=[(2*f,-1),(2*f,1)]
    elif k=='S': step=[(f,-1),(f,0),(f,1),(-f,-1),(-f,1)]
    elif k=='L': ray=[(f,0)]
    elif k=='B': ray=diag; step=orth if prom else []
    elif k=='R': ray=orth; step=diag if prom else []
    r,c=divmod(src,9)
    for dr,dc in step:
        rr,cc=r+dr,c+dc
        if 0<=rr<9 and 0<=cc<9: yield rr*9+cc
    for dr,dc in ray:
        rr,cc=r+dr,c+dc
        while 0<=rr<9 and 0<=cc<9:
            dst=rr*9+cc; yield dst
            if p.board[dst] is not None: break
            rr+=dr; cc+=dc

def checked(p,color):
    king=next((i for i,q in enumerate(p.board) if q and q[0]==color and q[1]=='K'),None)
    return king is None or any(king in targets(p,i) for i,q in enumerate(p.board) if q and q[0]!=color)
def dead(color,k,dst):
    r=dst//9 if color==0 else 8-dst//9
    return (k in 'PL' and r==0) or (k=='N' and r<=1)
def zone(color,s): return s//9<=2 if color==0 else s//9>=6

def board_moves(p):
    for src,q in enumerate(p.board):
        if not q or q[0]!=p.turn: continue
        color,k,pro=q
        for dst in targets(p,src):
            taken=p.board[dst]
            if taken and (taken[0]==color or taken[1]=='K'): continue
            if pro or not dead(color,k,dst): yield (src,dst,False,None)
            if not pro and k not in 'GK' and (zone(color,src) or zone(color,dst)):
                yield (src,dst,True,None)
def drops(p):
    for k,n in p.hands[p.turn].items():
        if not n: continue
        for dst,q in enumerate(p.board):
            if q or dead(p.turn,k,dst): continue
            if k=='P' and any(pc==(p.turn,'P',False) and i%9==dst%9 for i,pc in enumerate(p.board)): continue
            yield (None,dst,False,k)
def apply(p,m):
    src,dst,pro,k=m
    b=p.board.copy(); hands=[p.hands[0].copy(),p.hands[1].copy()]
    if src is None:
        hands[p.turn][k]-=1; b[dst]=(p.turn,k,False)
    else:
        if b[dst]:
            kk=b[dst][1]; hands[p.turn][kk]=hands[p.turn].get(kk,0)+1
        color,kk,pp=b[src]; b[src]=None; b[dst]=(color,kk,pp or pro)
    return Pos(b,1-p.turn,hands,p.number+1)
def usi(m):
    src,dst,pro,k=m
    return (k+'*'+usq(dst)) if src is None else usq(src)+usq(dst)+('+' if pro else '')
def legal(p):
    for m in list(board_moves(p))+list(drops(p)):
        nxt=apply(p,m)
        if checked(nxt,p.turn): continue
        if m[0] is None and m[3]=='P':
            king=next(i for i,q in enumerate(nxt.board) if q and q[:2]==(nxt.turn,'K'))
            if king in targets(nxt,m[1]) and not any(not checked(apply(nxt,x),nxt.turn) for x in board_moves(nxt)):
                continue
        yield m

def perft(p,d):
    return 1 if not d else sum(perft(apply(p,m),d-1) for m in legal(p))

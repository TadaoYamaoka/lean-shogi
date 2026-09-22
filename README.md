# Lean 4：SFENから合法手（USI形式）を列挙

将棋の局面をSFEN文字列で受け取り、その局面で指せる手をUSI形式で返す参照実装です。
処理本体はLean 4だけで記述しています。mathlib、FFI、外部将棋エンジンへの依存はありません。
`lean-toolchain` は `leanprover/lean4:v4.34.0` に固定しています。

## 検証状況 — 必ず確認してください

この作成環境にはLeanコンパイラがなく、配布物の取得もできなかったため、
**Leanコードのコンパイル・実行は未確認**です。実行確認済みの完成品という扱いではありません。

実施したのは、別途記述したレイ走査方式のPython補助モデルによる、
72局面の期待手集合・先後反転ケース・初期局面のperft(1)=30、perft(2)=900の確認です。
これはテストデータの整合性確認であり、Leanコードの動作確認や形式的証明の代わりではありません。
35件の不正SFENに対するLeanテストも用意していますが、そちらは未実行です。

`legalMoves` の健全性・完全性をLeanの定理として証明したものではありません。
`cshogi` と実際のLean実行結果を比較するスクリプトもありますが、この環境では未実行です。

## 実行

elan / Leanがインストール済みの環境で、ZIPを展開してプロジェクトディレクトリに移動します。

```sh
cd lean-shogi
lake build

# 平手初期局面
lake exe shogi --startpos

# 任意のSFEN。4フィールド全体を引用符で囲む
lake exe shogi "lnsgkgsnl/1r5b1/ppppppppp/9/9/9/PPPPPPPPP/1B5R1/LNSGKGSNL b - 1"

# 手数だけを表示。初期局面の期待値は30
lake exe shogi --count "lnsgkgsnl/1r5b1/ppppppppp/9/9/9/PPPPPPPPP/1B5R1/LNSGKGSNL b - 1"
```

通常出力は、空白区切りのUSI指し手を1行に並べたものです。
詰みなどで指せる手がなければ空行を返します。
初期局面の手集合は `tests/startpos_expected.txt` に辞書順で記載しています。
実際の列挙順は辞書順ではなく、盤面走査順です。順序は評価値を表しません。

エラー時は標準エラー出力に `error: ...` を表示し、終了コード2を返します。

### 単一ファイルで実行する場合

`ShogiMain.lean` は、本体とCLIを連結した単一ファイル版です。
Lean 4.34.0の環境なら、Lakeプロジェクトを作成せずに実行できます。

```sh
lean --run ShogiMain.lean "lnsgkgsnl/1r5b1/ppppppppp/9/9/9/PPPPPPPPP/1B5R1/LNSGKGSNL b - 1"
```

### Leanから呼び出す

```lean
import Shogi

#eval Shogi.legalMovesUSI Shogi.startSFEN
#eval (Shogi.legalMovesUSI Shogi.startSFEN).map List.length

def exampleMoves : Except String (List String) := do
  let p ← Shogi.parseSFEN Shogi.startSFEN
  let next ← Shogi.playUSI p "7g7f"
  return (Shogi.legalMoves next).map Shogi.Move.toUSI
```

公開APIは次のとおりです。

```lean
Shogi.parseSFEN        : String → Except String Shogi.Position
Shogi.legalMoves       : Shogi.Position → List Shogi.Move
Shogi.legalMovesUSI    : String → Except String (List String)
Shogi.playUSI          : Shogi.Position → String → Except String Shogi.Position
Shogi.toSFEN           : Shogi.Position → String
Shogi.validatePosition : Shogi.Position → Except String Unit
```

外部入力には `parseSFEN` または `legalMovesUSI` を使ってください。
手作業で構築した `Position` は、先に `validatePosition` で検証してください。
`applyUnchecked` は内部遷移用で、渡した手の合法性を検査しません。
外部から渡された指し手の適用には `play` / `playUSI` を使います。

### 複数局面・着手・perft

```sh
# stdinの1行につきSFENを1つ入力。stdoutの対応する1行がその合法手一覧
lake exe shogi --batch < positions.sfen

# 合法性を確認して1手進め、結果のSFENを出力
lake exe shogi --play "lnsgkgsnl/1r5b1/ppppppppp/9/9/9/PPPPPPPPP/1B5R1/LNSGKGSNL b - 1" "7g7f"

# 深さ2の葉局面数。初期局面の期待値は900
lake exe shogi --perft 2 "lnsgkgsnl/1r5b1/ppppppppp/9/9/9/PPPPPPPPP/1B5R1/LNSGKGSNL b - 1"
```

バッチモードでは、不正入力に `ERROR` とタブで始まる1行を返して処理を続けます。
不正入力が1件でもあれば、最後の終了コードは2になります。
このCLIはUSI形式の指し手を出力しますが、USIエンジンプロトコル全体を実装したものではありません。

## 対象ルールと入力条件

全駒の移動、飛・角・香の遮蔽、駒取り、成駒の持ち駒への戻し、持ち駒の打ちを扱います。
成・不成は合法なら両方列挙します。歩・香・桂の強制成りも判定します。
二歩、と金と同筋への歩打ちの許可、行き所のない駒打ち、自玉の王手放置、
ピン、両王手、王同士の接近、打ち歩詰めを扱います。
相手玉を直接取る手は列挙しません。盤上の歩を動かして詰ます「突き歩詰め」は除外しません。

入力は標準の4フィールドSFENです。`position sfen` の前置きや `moves` 節は受け取りません。
空白・タブ・CR・LFによるフィールド区切りを受け付けます。入力上限は4096バイトです。

盤面は必ず9×9で、玉は先後各1枚必要です。**片玉の詰将棋SFENは対象外**です。
王・金の成り、持ち駒の玉、二歩、行き所のない不成駒、
通常の将棋の総枚数を超える駒数、非手番側の玉に既に王手がかかった局面を拒否します。
駒落ち・作図局面用に、玉以外の総枚数が通常より少ないことは許容します。
手数フィールドは正の整数が必要です。これらは静的な整合性検査であって、
初期局面から本当に到達可能かどうかの証明ではありません。

**千日手・連続王手の千日手、持将棋や入玉宣言、時間切れ等の終局判定は対象外**です。
単一SFENには着手履歴がないため、反復に関する判定には別途履歴が必要です。
`resign` や `win` は通常着手一覧には含めません。
既に千日手等で終局したかどうかも、このAPI単独では判断しません。

## 実装の要点

`Square := Fin 81`、`Board := Vector (Option Piece) 81` により、
盤上座標の範囲と盤面の要素数を型で固定しています。
SFEN順に `0 = 9a`、`80 = 1i` とします。
外部の数値から座標を作るときは、範囲チェックをする `squareAt` を使用します。

`boardMoves` と `dropMoves` が候補手を列挙し、`applyUnchecked` で1手進め、
`inCheck` と `pawnDropMate` で不適合な手を除去します。
王手検査の利き判定は幾何学的な利きであり、ピンされた敵駒の利きも含めます。

歩打ちによる王手は玉の直前からの王手なので、合駒では解消できません。
そのため打ち歩詰めの検査では、相手の盤上の駒による応手だけを全列挙して自玉の安全を検査します。
相手玉の移動や歩の取りが1つでも可能なら、打ち歩詰めではありません。
この設計により、合法手生成の相互再帰や、任意の深さ制限を使わずに判定します。

読みやすさを優先した全升走査の参照実装です。
ビットボードや探索エンジン向けの高速化は行っていません。

## テスト

### 実際のLeanコードを検査

```sh
lake exe shogi-tests
```

72局面の合法手集合、35件の不正入力、SFEN往復変換、各合法手の適用後の整合性、
捕獲時の成り解除、持ち駒の減算、初期局面perft(0..2)を検査します。
先後を180度反転した局面も含みます。

### 外部ライブラリとの比較（任意）

```sh
python -m pip install cshogi
python tests/compare_cshogi.py --positions 1000 --seed 20260922
```

固定72局面と、cshogiの合法手でランダムに進めた1000局面について、
**実際のLeanバイナリ**の出力とcshogiの合法手集合を比較します。
外部ライブラリによるテストは任意であり、本体の実行依存ではありません。
この比較スクリプト自体も、この作成環境では実行していません。

### テストデータのみの補助確認

```sh
python tests/check_reference_model.py
```

これはこの作成環境で実行した確認です。Python標準ライブラリだけを使います。
**Leanコードを実行しているわけではありません。**

## ファイル

- `Shogi.lean`：データ型、パーサ、ルール、合法手生成、SFEN出力
- `Main.lean`：CLI
- `ShogiMain.lean`：本体とCLIを連結した単一ファイル版
- `Example.lean`：Lean / VS Codeでの呼び出し例
- `Tests.lean`：Leanの回帰テスト
- `tests/cases.json`：入力と期待手集合
- `tests/compare_cshogi.py`：実Leanバイナリとcshogiの差分テスト
- `tests/reference_model.py`、`tests/check_reference_model.py`：補助モデルによるテストデータ確認
- `lean-toolchain`、`lakefile.toml`：バージョンとビルド設定

## 参照仕様

SFEN / USI表記：
https://shogidokoro2.stars.ne.jp/usi.html

日本将棋連盟・対局規則：
https://www.shogi.or.jp/match/taikyoku_rules/

日本将棋連盟・反則：
https://www.shogi.or.jp/knowledge/shogi/05.php

LeanのLakeドキュメント：
https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/

Lean 4.34.0：
https://github.com/leanprover/lean4/releases/tag/v4.34.0

比較用cshogiの公式リポジトリ：
https://github.com/TadaoYamaoka/cshogi

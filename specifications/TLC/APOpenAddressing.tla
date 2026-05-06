------------------------------ MODULE APOpenAddressing ------------------------------
(* Apalache Snowcat type annotations for OpenAddressing.tla, applied via INSTANCE so
   the original spec stays free of tool-specific markup. *)

CONSTANT
  \* @type: Int;
  K,
  \* @type: Set(Int);
  fps,
  \* @type: Int;
  empty,
  \* @type: Set(Str);
  Writer,
  \* @type: Set(Str);
  Reader,
  \* @type: Int;
  L

VARIABLES
  \* @type: Int -> Int;
  table,
  \* @type: Seq(Int);
  external,
  \* @type: Seq(Int);
  newexternal,
  \* @type: Bool;
  evict,
  \* @type: Int;
  waitCnt,
  \* @type: Set(Int);
  history,
  \* @type: Str -> Str;
  pc,
  \* @type: Str -> Seq({ procedure: Str, pc: Str, ei: Int, ej: Int, lo: Int });
  stack,
  \* @type: Str -> Int;
  ei,
  \* @type: Str -> Int;
  ej,
  \* @type: Str -> Int;
  lo,
  \* @type: Str -> Int;
  fp,
  \* @type: Str -> Int;
  index,
  \* @type: Str -> Bool;
  result,
  \* @type: Str -> Int;
  expected

INSTANCE OpenAddressing

=============================================================================

import sigs.hb_smt
open smt
open smt.sort smt.term

@[simp] def letSort0 := atom "U"
@[simp] def f := const "f" (mkArrowN [letSort0, letSort0, letSort0])
@[simp] def a := const "a" letSort0
@[simp] def b := const "b" letSort0
@[simp] def c := const "c" letSort0
@[simp] def d := const "d" letSort0
@[simp] def fdb := mkAppN f [d, b]
@[simp] def faa := mkAppN f [a, a]
@[simp] def fcb := mkAppN f [c, b]

@[simp] def eqafcb := mkEq a fcb
@[simp] def neqafcb := mkNot $ mkEq a fcb

@[simp] def eqafdb := mkEq a fdb
@[simp] def neqafdb := mkNot eqafdb

@[simp] def eqfaafdb := mkEq faa fdb
@[simp] def neqfaafdb := mkNot $ mkEq faa fdb

@[simp] def eqfcbfaa := mkEq fcb faa
@[simp] def neqfcbfaa := mkNot $ mkEq fcb faa

@[simp] def eqfaafcb := mkEq faa fcb
@[simp] def neqfaafcb := mkNot $ mkEq faa fcb

#eval [neqafcb, neqfcbfaa, neqfaafdb, eqafdb]

noncomputable theorem main :
  th_holds ([neqafdb]) -> th_holds ([eqfaafdb]) -> th_holds ([eqfcbfaa]) -> th_holds ([eqafcb]) -> th_holds([]) :=
assume s0 : th_holds ([neqafdb]),
assume s1 : th_holds ([eqfaafdb]),
assume s2 : th_holds ([eqfcbfaa]),
assume s3 : th_holds ([eqafcb]),
have s5 : th_holds ([neqafcb, neqfcbfaa, neqfaafdb, eqafdb]),
  from @smttransn [a, fcb, faa, fdb],
show th_holds ([]),
  from R1 (R1 (R1 (R0 s5 s0 eqafdb) s1 eqfaafdb) s2 eqfcbfaa) s3 eqafcb

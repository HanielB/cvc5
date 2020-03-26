import sigs.mysmt

open mysmt

open mysmt.sort mysmt.myterm mysmt.myformula

@[simp] def A := atom "A"
@[simp] def B := atom "B"

@[simp] def a := const "a" A
@[simp] def b := const "b" A
@[simp] def f := const "f" (arrow A A)

@[simp] def fa := mkApp f a
@[simp] def fb := mkApp f b

@[simp] def eqab := mkEq a b
@[simp] def neqab := mkNot eqab
@[simp] def eqff := mkEq f f
@[simp] def neqff := mkNot eqff
@[simp] def eqfafb := mkEq fa fb
@[simp] def neqfafb := mkNot eqfafb

noncomputable theorem teo : th_holds ([eqab]) -> th_holds ([neqfafb]) -> th_holds ([]) :=
assume s0 : th_holds ([eqab]),
assume s1 : th_holds ([neqfafb]),
have s2   : th_holds ([eqff]), from smtrefl f,
have s3   : th_holds ([neqff, neqab, eqfafb]), from smtcong,
have s4   : th_holds ([neqab, eqfafb]), from fo_R s2 s3 eqff,
have s5   : th_holds ([eqfafb]), from fo_R s0 s4 eqab,
show th_holds [], from fo_R s5 s1 eqfafb

import sigs.mysmt

open mysmt

open mysmt.sort mysmt.myterm mysmt.myformula

@[simp] def A := atom "A"

@[simp] def f1 := const "f1" A
@[simp] def f2 := const "f2" A
@[simp] def f3 := const "f3" A
@[simp] def f4 := const "f4" A
@[simp] def p := const "p" (mkArrowN [A, boolsort])

@[simp] def pf1 := mkPapp p f1
@[simp] def npf1 := mkNot pf1
@[simp] def pf3 := mkPapp p f3
@[simp] def npf3 := mkNot pf3

@[simp] def eqf1f2 := mkEq f1 f2
@[simp] def neqf1f2 := mkNot eqf1f2

@[simp] def eqf3f4 := mkEq f3 f4
@[simp] def neqf3f4 := mkNot eqf3f4
@[simp] def eqf3f2 := mkEq f3 f2
@[simp] def neqf3f2 := mkNot eqf3f2
@[simp] def eqf4f2 := mkEq f4 f2
@[simp] def neqf4f2 := mkNot eqf4f2

@[simp] def distf3f4f2 := mkDistinct [f3, f4, f2]
@[simp] def ndistf3f4f2 := mkNot distf3f4f2
@[simp] def or0 := mkOrN [eqf1f2, distf3f4f2]
@[simp] def nor0 := mkNot or0
@[simp] def imp0 := mkImplies or0 pf3
@[simp] def nimp0 := mkNot imp0
@[simp] def imp1 := mkImplies pf1 imp0

#eval distf3f4f2
#eval ndistf3f4f2

noncomputable theorem teo :
    th_holds ([eqf1f2]) -> th_holds ([imp1]) -> th_holds ([pf1]) -> th_holds ([npf3]) → th_holds ([]) :=
assume s0 : th_holds ([eqf1f2]),
assume s1 : th_holds ([imp1]),
assume s2 : th_holds ([pf1]),
assume s3 : th_holds ([npf3]),
have sbb   : th_holds ([ndistf3f4f2, neqf3f2]), from @cnf_and_pos [neqf4f2, neqf3f4, neqf3f2] 2,
have s4   : th_holds ([or0, neqf1f2]), from @cnf_or_neg [eqf1f2, distf3f4f2] 0,
have s5   : th_holds ([nimp0, nor0, pf3]), from cnf_implies_pos,
have s6   : th_holds ([imp0, npf3]), from cnf_implies_neg_1,
have s7   : th_holds ([npf1, imp0]), from cnf_implies s1,
have s8   : th_holds ([imp0]), from fo_R s2 s7 pf1,
have s9   : th_holds ([or0]), from fo_R s0 s4 eqf1f2,
have s10  : th_holds ([nimp0, pf3]), from fo_R s9 s5 or0,
have s11  : th_holds ([pf3]), from fo_R s8 s10 imp0,
show th_holds [], from fo_R s11 s3 pf3

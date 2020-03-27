import sigs.mysmt

open mysmt

open mysmt.sort mysmt.myterm mysmt.myformula

@[simp] def A := atom "A"

@[simp] def a := const "a" A
@[simp] def b := const "b" A
@[simp] def p := const "p" (mkArrowN [A, boolsort])

@[simp] def pa := mkPapp p a
@[simp] def npa := mkNot pa

@[simp] def iteterm := mkIte pa b a
@[simp] def eqbite := mkEq b iteterm
@[simp] def neqbite := mkNot eqbite

@[simp] def imp0 := mkImplies pa eqbite

noncomputable theorem teo :
    th_holds ([pa]) -> th_holds ([neqbite]) -> th_holds ([]) :=
assume s0 : th_holds ([pa]),
assume s1 : th_holds ([neqbite]),
have s2   : th_holds ([imp0]), from @ite_intro_0 iteterm,
have s3   : th_holds ([npa, eqbite]), from cnf_implies s2,
have s4   : th_holds ([eqbite]), from fo_R s0 s3 pa,
show th_holds [], from fo_R s4 s1 eqbite

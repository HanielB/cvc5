import sigs.hb_smt

open mysmt

open mysmt.sort mysmt.term

@[simp] def A := atom "A"

@[simp] def a := const "a" A
@[simp] def b := const "b" A
@[simp] def p := const "p" (mkArrowN [A, boolsort])

@[simp] def pa := mkApp p a
@[simp] def npa := mkNot pa

@[simp] def iteterm := mkIte pa b a
@[simp] def eqbite := mkEq b iteterm
@[simp] def neqbite := mkNot eqbite
@[simp] def eqaite := mkEq a iteterm
@[simp] def neqaite := mkNot eqaite
@[simp] def itedef := mkIte pa eqbite eqaite
@[simp] def nitedef := mkNot itedef

#eval itedef
#eval nitedef
#eval [nitedef, npa, eqbite]

#eval mkNot itedef

#eval iteterm

noncomputable theorem teo :
    th_holds ([pa]) -> th_holds ([neqbite]) -> th_holds ([]) :=
assume s0 : th_holds ([pa]),
assume s1 : th_holds ([neqbite]),
have s2   : th_holds ([itedef]), from @ite_intro iteterm,
have s3   : th_holds ([nitedef, npa, eqbite]), from cnf_ite_pos_0,
have s4   : th_holds ([npa, eqbite]), from fo_R s2 s3 itedef,
have s5   : th_holds ([eqbite]), from fo_R s0 s4 pa,
show th_holds [], from fo_R s5 s1 eqbite

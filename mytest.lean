import sigs.mysmt
import init.meta.tactic

open mysmt

open mysmt.sort

open mysmt.myterm

open mysmt.myformula

@[simp] def A := atom "A"
@[simp] def B := atom "B"

@[simp] def a := const "a" A
@[simp] def b := const "b" A
@[simp] def c := const "c" A
@[simp] def d := const "d" A
@[simp] def f := const "f" (arrow A A)
@[simp] def p := const "p" (arrow A boolsort)

@[simp] def fa := mkApp f a
@[simp] def fb := mkApp f b

@[simp] def eqab := mkEq a b
@[simp] def neqab := mkNot eqab
@[simp] def eqff := mkEq f f
@[simp] def neqff := mkNot eqff
@[simp] def eqfafb := mkEq fa fb
@[simp] def neqfafb := mkNot eqfafb

noncomputable theorem teo : th_holds ([neqfafb]) -> th_holds ([eqab]) -> th_holds ([]) :=
assume s0 : th_holds ([neqfafb]),
assume s1 : th_holds ([eqab]),
have s2   : th_holds ([eqff]), from smtrefl f,
have s3   : th_holds ([neqff, neqab, eqfafb]), from smtcong,
have s4   : th_holds ([neqab, eqfafb]), from fo_R s2 s3 eqff,
have s5   : th_holds ([eqfafb]), from fo_R s1 s4 eqab,
show th_holds [], from fo_R s5 s0 eqfafb

constant
    myfo_R : Π {c₁ c₂ : fo_clause} (p₁ : th_holds c₁) (p₂ : th_holds c₂) (n : myformula) {c : fo_clause},
        fo_resolveR n c₁ c₂ = c -> th_holds c

constant
    myfo_Q : Π {c₁ c₂ : fo_clause} (p₁ : th_holds c₁) (p₂ : th_holds c₂) (n : myformula) {c : fo_clause},
       fo_resolveQ n c₁ c₂ = c -> th_holds c

constant fo_satlem {c₁ c₂ c₃ : fo_clause} (p₁ : c₁ = c₂) (p₁₂ : c₁ = c₂ → th_holds c₃) : th_holds c₃

noncomputable theorem teo_old : th_holds ([neqfafb]) -> th_holds ([eqab]) -> th_holds ([]) :=
assume s0 : th_holds ([neqfafb]),
assume s1 : th_holds ([eqab]),
have s2   : th_holds ([eqff]), from smtrefl f,
have s3   : th_holds ([neqff, neqab, eqfafb]), from smtcong,
have pre_s4_0 : fo_resolveR eqff [eqff] [neqff, neqab, eqfafb] =
                [neqab, eqfafb] :=
                begin
                simp [fo_resolveR, concat_fo_cl, remove]
                end,
have pre_s4_1 : fo_resolveR eqff [eqff] [neqff, neqab, eqfafb] =
                [neqab, eqfafb] -> th_holds [neqab, eqfafb],
                from myfo_R s2 s3 eqff,
have s4       : th_holds ([neqab, eqfafb]), from fo_satlem pre_s4_0 pre_s4_1,
have pre_s5_0 : fo_resolveR eqab [eqab] [neqab, eqfafb] =
                [eqfafb] :=
                begin
                simp [fo_resolveR, concat_fo_cl, remove],
                end,
have pre_s5_1 : fo_resolveR eqab [eqab] [neqab, eqfafb] =
                [eqfafb] -> th_holds [eqfafb],
                from myfo_R s1 s4 eqab,
have s5       : th_holds ([eqfafb]), from fo_satlem pre_s5_0 pre_s5_1,
have pre_s6_0 : fo_resolveR (eqfafb) [eqfafb] [neqfafb] = [] :=
                begin
                simp [fo_resolveR, concat_fo_cl, remove],
                end,
have pre_s6_1 : fo_resolveR (eqfafb) [eqfafb] [neqfafb] = []
                -> th_holds [],
                from myfo_R s5 s0 (eqfafb),
show th_holds [], from fo_satlem pre_s6_0 pre_s6_1

@[simp] def reduce_smtcongn : list myterm → list myterm → fo_clause
| (h₁::t₁) (h₂::t₂) := (mynot $ myeq h₁ h₂) :: reduce_smtcongn t₁ t₂
| _ _ := []

constant smtcongn : Π {f : myterm} {a₁ a₂ : list myterm} ,
        th_holds (list.append (reduce_smtcongn a₁ a₂)
                   [mkEq (mkAppN f a₁) (mkAppN f a₂)])

constant smtcongn2 : Π {f : myterm} {a₁ a₂ : list myterm} ,
        th_holds ((mkEq (mkAppN f a₁) (mkAppN f a₂))::(reduce_smtcongn a₁ a₂))

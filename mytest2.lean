import sigs.mysmt
import init.meta.tactic

open mysmt

open mysmt.sort

open mysmt.myterm

open mysmt.myformula


-- noncomputable theorem teo (wut : atom "A") (a : const "a" A) (b : const "b" wut) (f : const "f" (arrow wut wut)) : th_holds ([mynot $ myeq (apply f a) (apply f b)]) -> th_holds ([myeq a b]) -> th_holds ([]) :=

variable mysort : sort

@[simp] theorem aux (t : myformula) : t ≠ myformula.undef → mkNot t = mynot t := sorry

@[simp] def A := atom "A"
@[simp] def B := atom "B"
@[simp] def a := const "a" A
@[simp] def b := const "b" A
@[simp] def f := const "f" (arrow A A)

constant
  myfo_R : Π {c₁ c₂ : fo_clause} (p₁ : th_holds c₁) (p₂ : th_holds c₂) (n : myformula) {c : fo_clause},
       fo_resolveR n c₁ c₂ = c -> th_holds c

constant
  myfo_Q : Π {c₁ c₂ : fo_clause} (p₁ : th_holds c₁) (p₂ : th_holds c₂) (n : myformula) {c : fo_clause},
       fo_resolveQ n c₁ c₂ = c -> th_holds c

constant fo_satlem {c₁ c₂ c₃ : fo_clause} (p₁ : c₁ = c₂) (p₁₂ : c₁ = c₂ → th_holds c₃) : th_holds c₃

constant smtrefl1 (t : myterm) : th_holds [myeq t t]

constant smtcong1 : Π {a₁ b₁ : myterm} {a₂ b₂ : myterm},
                      th_holds ([mynot (myeq a₁ b₁), mynot (myeq a₂ b₂),
                                       myeq (apply a₁ a₂) (apply b₁ b₂)])

noncomputable theorem teo :
  th_holds ([mynot $ myeq (apply f a) (apply f b)]) -> th_holds ([myeq a b]) -> th_holds ([]) :=
let
  eqab := (myeq a b),
  neqab := mynot eqab,
  eqfafb := myeq (apply f a) (apply f b),
  neqfafb := mynot eqfafb,
  eqff := myeq f f,
  neqff := mynot eqff
in
assume s0 : th_holds ([neqfafb]),
assume s1 : th_holds ([eqab]),
have s2   : th_holds ([eqff]), from smtrefl1 f,
have s3   : th_holds ([neqff, neqab, eqfafb]), from smtcong1,
have pre_s4_0 : fo_resolveR eqff [eqff] [neqff, neqab, eqfafb] =
                [neqab, eqfafb] :=
                begin
                simp [fo_resolveR, concat_fo_cl, remove],
                rewrite if_pos,

                end,
have pre_s4_1 : fo_resolveR eqff [eqff] [neqff, neqab, eqfafb] =
                [neqab, eqfafb] -> th_holds [neqab, eqfafb],
                from myfo_R s2 s3 eqff,
have s4       : th_holds ([neqab, eqfafb]), from fo_satlem pre_s4_0 pre_s4_1,
have pre_s5_0 : fo_resolveR eqab [eqab] [neqab, eqfafb] =
                [eqfafb] :=
                begin
                simp [fo_resolveR, concat_fo_cl, remove],
                rewrite if_pos,
                end,
have pre_s5_1 : fo_resolveR eqab [eqab] [neqab, eqfafb] =
                [eqfafb] -> th_holds [eqfafb],
                from myfo_R s1 s4 eqab,
have s5       : th_holds ([eqfafb]), from fo_satlem pre_s5_0 pre_s5_1,
have pre_s6_0 : fo_resolveR (eqfafb) [eqfafb] [neqfafb] = [] :=
                begin
                simp [fo_resolveR, concat_fo_cl, remove],
                rewrite if_pos,
                end,
have pre_s6_1 : fo_resolveR (eqfafb) [eqfafb] [neqfafb] = []
                -> th_holds [],
                from myfo_R s5 s0 (eqfafb),
show th_holds [], from fo_satlem pre_s6_0 pre_s6_1

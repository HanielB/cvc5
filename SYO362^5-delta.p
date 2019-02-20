%------------------------------------------------------------------------------
% File     : SYO362^5 : TPTP v7.2.0. Released v4.0.0.
% Domain   : Syntactic
% Problem  : TPS problem THM631A
% Version  : Especial.
% English  : If a set function preserves unions, then it is monotone.

% Refs     : [Bro09] Brown (2009), Email to Geoff Sutcliffe
% Source   : [Bro09]
% Names    : tps_0419 [Bro09]
%          : THM631 [TPS]
%          : THM631A [TPS]

% Status   : Theorem
% Rating   : 0.22 v7.2.0, 0.12 v7.1.0, 0.25 v7.0.0, 0.14 v6.4.0, 0.17 v6.3.0, 0.20 v6.2.0, 0.29 v6.1.0, 0.14 v6.0.0, 0.29 v5.5.0, 0.50 v5.4.0, 0.60 v5.3.0, 0.80 v4.1.0, 1.00 v4.0.0
% Syntax   : Number of formulae    :    2 (   0 unit;   1 type;   0 defn)
%            Number of atoms       :   22 (   1 equality;  16 variable)
%            Maximal formula depth :    9 (   6 average)
%            Number of connectives :   19 (   0   ~;   2   |;   0   &;  13   @)
%                                         (   0 <=>;   4  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    7 (   7   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    3 (   1   :;   0   =)
%            Number of variables   :    8 (   0 sgn;   6   !;   0   ?;   2   ^)
%                                         (   8   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU_NAR

% Comments : This problem is from the TPS library. Copyright (c) 2009 The TPS
%            project in the Department of Mathematical Sciences at Carnegie
%            Mellon University. Distributed under the Creative Commons copyleft
%            license: http://creativecommons.org/licenses/by-sa/3.0/
%          : Polymorphic definitions expanded.
%          :
%------------------------------------------------------------------------------
thf(cK,type,(
    cK: ( $i > $o ) > $i > $o )).

thf(cTHM631A_pme,conjecture,
    ( ! [X: $i > $o,Y: $i > $o] :
        ( ( cK
          @ ^ [Xz: $i] :
              ( ( X @ Xz )
              | ( Y @ Xz ) ) )
        = ( ^ [Xw: $i] :
              ( ( cK @ X @ Xw )
              | ( cK @ Y @ Xw ) ) ) )
   => ! [X: $i > $o,Y: $i > $o] :
        ( ! [Xx: $i] :
            ( ( X @ Xx )
           => ( Y @ Xx ) )
       => ! [Xx: $i] :
            ( ( cK @ X @ Xx )
           => ( cK @ Y @ Xx ) ) ) )).

%------------------------------------------------------------------------------

%% soundness issue due to wrong lambda lifting. Free variables in
%% lambda body not being carried out to quantified formula standing
%% for lambda lifting

%% (not
%%  (=>
%%    (forall ((X (-> $$unsorted Bool)) (Y (-> $$unsorted Bool)))
%%      (=
%%        (lambda ((Xw $$unsorted)) (or (cK X Xw) (cK Y Xw)))
%%        (cK (lambda ((Xz $$unsorted)) (or (X Xz) (Y Xz))))))
%%    (forall ((X (-> $$unsorted Bool)) (Y (-> $$unsorted Bool)) (BOUND_VARIABLE_341 $$unsorted))
%%      (or
%%        (not (forall ((Xx $$unsorted)) (or (not (X Xx)) (Y Xx)) ))
%%        (not (cK X BOUND_VARIABLE_341)) (cK Y BOUND_VARIABLE_341)) )))

%% ; lambda-lifted into

%% (not
%%  (=>
%%    (forall ((X (-> $$unsorted Bool)) (Y (-> $$unsorted Bool)))
%%      (= llf_2 (cK llf_1)) )
%%    (forall ((X (-> $$unsorted Bool)) (Y (-> $$unsorted Bool)) (BOUND_VARIABLE_341 $$unsorted))
%%      (or
%%        (not (forall ((Xx $$unsorted)) (or (not (X Xx)) (Y Xx)) ))
%%        (not (cK X BOUND_VARIABLE_341)) (cK Y BOUND_VARIABLE_341)) )))


%% (forall ((BOUND_VARIABLE_364 $$unsorted)) (= (llf_2 BOUND_VARIABLE_364) (or (cK X BOUND_VARIABLE_364) (cK Y BOUND_VARIABLE_364))) )

%% (forall ((BOUND_VARIABLE_372 $$unsorted)) (= (llf_1 BOUND_VARIABLE_372) (or (X BOUND_VARIABLE_372) (Y BOUND_VARIABLE_372))) )

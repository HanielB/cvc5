%------------------------------------------------------------------------------
% File     : SEU989^5 : TPTP v7.2.0. Released v4.0.0.
% Domain   : Set Theory (Relations)
% Problem  : TPS problem from GRAPHS-THMS
% Version  : Especial.
% English  :

% Refs     : [Bro09] Brown (2009), Email to Geoff Sutcliffe
% Source   : [Bro09]
% Names    : tps_1059 [Bro09]

% Status   : Unknown
% Rating   : 1.00 v4.0.0
% Syntax   : Number of formulae    :    3 (   0 unit;   2 type;   0 defn)
%            Number of atoms       :   36 (   3 equality;  33 variable)
%            Maximal formula depth :   12 (   5 average)
%            Number of connectives :   29 (   0   ~;   0   |;   7   &;  18   @)
%                                         (   0 <=>;   4  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    4 (   4   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    4 (   2   :;   0   =)
%            Number of variables   :   17 (   0 sgn;  12   !;   5   ?;   0   ^)
%                                         (  17   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_UNK_EQU_NAR

% Comments : This problem is from the TPS library. Copyright (c) 2009 The TPS
%            project in the Department of Mathematical Sciences at Carnegie
%            Mellon University. Distributed under the Creative Commons copyleft
%            license: http://creativecommons.org/licenses/by-sa/3.0/
%          :
%------------------------------------------------------------------------------
thf(b_type,type,(
    b: $tType )).

thf(a_type,type,(
    a: $tType )).

thf(cTHM554_pme,conjecture,
    ( ? [S: b > a > $o] :
        ( ! [Xx: b] :
          ? [Xy: a] :
            ( S @ Xx @ Xy )
        & ! [Xx: b,Xy1: a,Xy2: a] :
            ( ( ( S @ Xx @ Xy1 )
              & ( S @ Xx @ Xy2 ) )
           => ( Xy1 = Xy2 ) )
        & ! [Xx1: b,Xx2: b,Xy: a] :
            ( ( ( S @ Xx1 @ Xy )
              & ( S @ Xx2 @ Xy ) )
           => ( Xx1 = Xx2 ) ) )
   => ? [R: a > b > $o] :
        ( ! [Xx: a] :
          ? [Xy: b] :
            ( R @ Xx @ Xy )
        & ! [Xy: b] :
          ? [Xx: a] :
            ( R @ Xx @ Xy )
        & ! [Xx: a,Xy1: b,Xy2: b] :
            ( ( ( R @ Xx @ Xy1 )
              & ( R @ Xx @ Xy2 ) )
           => ( Xy1 = Xy2 ) ) ) )).

%------------------------------------------------------------------------------

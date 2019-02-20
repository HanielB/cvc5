%------------------------------------------------------------------------------
% File     : QUA007^1 : TPTP v7.2.0. Released v4.1.0.
% Domain   : Quantales
% Problem  : Right-distributivity of multiplication over addition
% Version  : [Hoe09] axioms.
% English  :

% Refs     : [Con71] Conway (1971), Regular Algebra and Finite Machines
%          : [Hoe09] Hoefner (2009), Email to Geoff Sutcliffe
% Source   : [Hoe09]
% Names    : QUA07 [Hoe09]

% Status   : Theorem
% Rating   : 1.00 v4.1.0
% Syntax   : Number of formulae    :   27 (   0 unit;  12 type;   7 defn)
%            Number of atoms       :  104 (  18 equality;  47 variable)
%            Maximal formula depth :   12 (   5 average)
%            Number of connectives :   53 (   0   ~;   1   |;   4   &;  47   @)
%                                         (   1 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :   43 (  43   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   15 (  12   :;   0   =)
%            Number of variables   :   30 (   1 sgn;  11   !;   4   ?;  15   ^)
%                                         (  30   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU_NAR

% Comments :
%------------------------------------------------------------------------------
%----Include axioms for Quantales
%% include('Axioms/QUA001^0.ax').
%------------------------------------------------------------------------------
thf(sup_type,type,(
    sup: ( $i > $o ) > $i )).

thf(union_type,type,(
    union: ( $i > $o ) > ( $i > $o ) > $i > $o )).

thf(union_def,definition,
    ( union
    = ( ^ [X: $i > $o,Y: $i > $o,U: $i] :
          ( ( X @ U )
          | ( Y @ U ) ) ) )).

thf(singleton_type,type,(
    singleton: $i > $i > $o )).

thf(singleton_def,definition,
    ( singleton
    = ( ^ [X: $i,U: $i] : ( U = X ) ) )).

thf(multiplication_type,type,(
    multiplication: $i > $i > $i )).

thf(addition_type,type,(
    addition: $i > $i > $i )).

thf(addition_def,definition,
    ( addition
    = ( ^ [X: $i,Y: $i] :
          ( sup @ ( union @ ( singleton @ X ) @ ( singleton @ Y ) ) ) ) )).


thf(multiplication_distrr,conjecture,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( multiplication @ X1 @ ( addition @ X2 @ X3 ) )
      = ( addition @ ( multiplication @ X1 @ X2 ) @ ( multiplication @ X1 @ X3 ) ) ) )).

%------------------------------------------------------------------------------

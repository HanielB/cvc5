%------------------------------------------------------------------------------
% File     : SEU807^2 : TPTP v7.2.0. Released v3.7.0.
% Domain   : Set Theory
% Problem  : The Foundation Axiom
% Version  : Especial > Reduced > Especial.
% English  : (! A:i.! B:i.in A B -> ~(in B A))

% Refs     : [Bro08] Brown (2008), Email to G. Sutcliffe
% Source   : [Bro08]
% Names    : ZFC309l [Bro08]

% Status   : Theorem
% Rating   : 0.22 v7.2.0, 0.12 v7.1.0, 0.38 v7.0.0, 0.43 v6.4.0, 0.50 v6.3.0, 0.60 v6.2.0, 0.43 v5.5.0, 0.50 v5.4.0, 0.60 v5.1.0, 0.80 v5.0.0, 0.60 v4.1.0, 0.33 v4.0.1, 0.67 v4.0.0, 0.33 v3.7.0
% Syntax   : Number of formulae    :   14 (   0 unit;   8 type;   5 defn)
%            Number of atoms       :   71 (   9 equality;  35 variable)
%            Maximal formula depth :   12 (   6 average)
%            Number of connectives :   49 (   2   ~;   1   |;   2   &;  32   @)
%                                         (   1 <=>;  11  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    4 (   4   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   10 (   8   :;   0   =)
%            Number of variables   :   18 (   0 sgn;  15   !;   3   ?;   0   ^)
%                                         (  18   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU_NAR

% Comments : http://mathgate.info/detsetitem.php?id=436
%          :
%------------------------------------------------------------------------------
%% test type
thf(meq_prop_type,type,(
    meq_prop: ( $i > $o ) > ( $i > $o ) > $i > $o )).


thf(in_type,type,(
    in: $i > $i > $o )).

thf(emptyset_type,type,(
    emptyset: $i )).



thf(setadjoin_type,type,(
    setadjoin: $i > $i > $i )).

thf(foundationAx_type,type,(
    foundationAx: $o )).

%% thf(foundationAx,definition,
%%     ( foundationAx
%%     = ( ! [A: $i] :
%%           ( ? [Xx: $i] :
%%               ( in @ Xx @ A )
%%          => ? [B: $i] :
%%               ( ( in @ B @ A )
%%               & ~ ( ? [Xx: $i] :
%%                       ( ( in @ Xx @ B )
%%                       & ( in @ Xx @ A ) ) ) ) ) ) )).

thf(setadjoinIL_type,type,(
    setadjoinIL: $o )).

%% thf(setadjoinIL,definition,
%%     ( setadjoinIL
%%     = ( ! [Xx: $i,Xy: $i] :
%%           ( in @ Xx @ ( setadjoin @ Xx @ Xy ) ) ) )).

thf(setadjoinIR_type,type,(
    setadjoinIR: $o )).

%% thf(setadjoinIR,definition,
%%     ( setadjoinIR
%%     = ( ! [Xx: $i,A: $i,Xy: $i] :
%%           ( ( in @ Xy @ A )
%%          => ( in @ Xy @ ( setadjoin @ Xx @ A ) ) ) ) )).

thf(in__Cong_type,type,(
    in__Cong: $o )).

%% thf(in__Cong,definition,
%%     ( in__Cong
%%     = ( ! [A: $i,B: $i] :
%%           ( ( A = B )
%%          => ! [Xx: $i,Xy: $i] :
%%               ( ( Xx = Xy )
%%              => ( ( in @ Xx @ A )
%%               <=> ( in @ Xy @ B ) ) ) ) ) )).

thf(upairset2E_type,type,(
    upairset2E: $o )).

%% thf(upairset2E,definition,
%%     ( upairset2E
%%     = ( ! [Xx: $i,Xy: $i,Xz: $i] :
%%           ( ( in @ Xz @ ( setadjoin @ Xx @ ( setadjoin @ Xy @ emptyset ) ) )
%%          => ( ( Xz = Xx )
%%             | ( Xz = Xy ) ) ) ) )).

%% thf(notinself2,conjecture,
%%     ( foundationAx
%%    => ( setadjoinIL
%%      => ( setadjoinIR
%%        => ( in__Cong
%%          => ( upairset2E
%%            => ! [A: $i,B: $i] :
%%                 ( ( in @ A @ B )
%%                => ~ ( in @ B @ A ) ) ) ) ) ) )).

%------------------------------------------------------------------------------

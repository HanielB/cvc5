%------------------------------------------------------------------------------
% File     : CSR135^2 : TPTP v7.2.0. Released v4.1.0.
% Domain   : Commonsense Reasoning
% Problem  : What's a common feeling of Sue and Mary to Bill?
% Version  : Especial > Augmented > Especial.
% English  : Does there exists a relation ?R that holds between Sue and Bill
%            as well as between Mary and Bill?

% Refs     : [Ben10] Benzmueller (2010), Email to Geoff Sutcliffe
% Source   : [Ben10]
% Names    : rv_1.tq_SUMO_sine [Ben10]

% Status   : Theorem
% Rating   : 0.10 v7.2.0, 0.12 v7.1.0, 0.14 v7.0.0, 0.12 v6.4.0, 0.14 v6.3.0, 0.17 v6.1.0, 0.33 v6.0.0, 0.00 v5.3.0, 0.25 v5.2.0, 0.00 v4.1.0
% Syntax   : Number of formulae    :   21 (   0 unit;   9 type;   0 defn)
%            Number of atoms       :   41 (   0 equality;   2 variable)
%            Maximal formula depth :    5 (   3 average)
%            Number of connectives :   29 (   0   ~;   0   |;   1   &;  28   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    6 (   6   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   13 (   9   :;   0   =)
%            Number of variables   :    1 (   0 sgn;   0   !;   1   ?;   0   ^)
%                                         (   1   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_NEQ_NAR

% Comments : This is a simple test problem for reasoning in/about SUMO.
%            Initally the problem has been hand generated in KIF syntax in
%            SigmaKEE and then automatically translated by Benzmueller's
%            KIF2TH0 translator into THF syntax.
%          : The translation has been applied in two modes: local and SInE.
%            The local mode only translates the local assumptions and the
%            query. The SInE mode additionally translates the SInE-extract
%            of the loaded knowledge base (usually SUMO).
%          : The examples are selected to illustrate the benefits of
%            higher-order reasoning in ontology reasoning.
%------------------------------------------------------------------------------
%----The extracted signature
thf(numbers,type,(
    num: $tType )).

thf(lAnna_THFTYPE_i,type,(
    lAnna_THFTYPE_i: $i )).

thf(lBen_THFTYPE_i,type,(
    lBen_THFTYPE_i: $i )).

thf(lBill_THFTYPE_i,type,(
    lBill_THFTYPE_i: $i )).

thf(lBob_THFTYPE_i,type,(
    lBob_THFTYPE_i: $i )).

thf(lMary_THFTYPE_i,type,(
    lMary_THFTYPE_i: $i )).

thf(lSue_THFTYPE_i,type,(
    lSue_THFTYPE_i: $i )).

thf(likes_THFTYPE_IiioI,type,(
    likes_THFTYPE_IiioI: $i > $i > $o )).

thf(parent_THFTYPE_IiioI,type,(
    parent_THFTYPE_IiioI: $i > $i > $o )).

%----The translated axioms
thf(ax,axiom,
    ( likes_THFTYPE_IiioI @ lSue_THFTYPE_i @ lBill_THFTYPE_i )).

thf(ax_001,axiom,
    ( likes_THFTYPE_IiioI @ lSue_THFTYPE_i @ lBill_THFTYPE_i )).

thf(ax_002,axiom,
    ( (~) @ ( likes_THFTYPE_IiioI @ lSue_THFTYPE_i @ lMary_THFTYPE_i ) )).

thf(ax_003,axiom,
    ( (~) @ ( likes_THFTYPE_IiioI @ lSue_THFTYPE_i @ lMary_THFTYPE_i ) )).

thf(ax_004,axiom,
    ( likes_THFTYPE_IiioI @ lMary_THFTYPE_i @ lBill_THFTYPE_i )).

thf(ax_005,axiom,
    ( likes_THFTYPE_IiioI @ lMary_THFTYPE_i @ lBill_THFTYPE_i )).

thf(ax_006,axiom,
    ( parent_THFTYPE_IiioI @ lMary_THFTYPE_i @ lBen_THFTYPE_i )).

thf(ax_007,axiom,
    ( parent_THFTYPE_IiioI @ lSue_THFTYPE_i @ lBen_THFTYPE_i )).

thf(ax_008,axiom,
    ( likes_THFTYPE_IiioI @ lBob_THFTYPE_i @ lBill_THFTYPE_i )).

thf(ax_009,axiom,
    ( parent_THFTYPE_IiioI @ lSue_THFTYPE_i @ lAnna_THFTYPE_i )).

thf(ax_010,axiom,
    ( parent_THFTYPE_IiioI @ lMary_THFTYPE_i @ lAnna_THFTYPE_i )).

%----The translated conjecture
thf(con,conjecture,(
    ? [R: $i > $i > $o] :
      ( ( R @ lSue_THFTYPE_i @ lBill_THFTYPE_i )
      & ( R @ lMary_THFTYPE_i @ lBill_THFTYPE_i ) ) )).

%------------------------------------------------------------------------------

$(
  lof.mm    version 0.1.1    Copyright (C) 2015 naipmoro
  This file is made available under the MIT License:
  http://opensource.org/licenses/MIT

  lof.mm presents metamath derivations of the Primary Algebra from
  Spencer-Brown, G. (1969) Laws of Form (Allen & Unwin, London),
  hereafter cited as LoF.

  The algebra of LoF has a number of models, most significantly Boolean
  algebra and sentential logic, so it may be of some interest to logicians.
  From the perspective of metamath, it is a non-trivial example of a system
  that requires, indeed is based on, the empty substitution.

  Access to the empty substitution, in conjunction with metamath's radical
  formalism, allows a representation that closely matches LoF's actual
  expressions.

  LoF is a 2-dimensional notation in which closed curves (boundaries) are the
  symbols under investigation, and in which the only property of interest
  is whether a given boundary is inside or outside of another boundary,
  intersecting boundaries not being allowed. Variables p q r ... will range
  over possible arrangements of boundaries (which we call 'forms'). It is now
  common to call LoF a 'boundary algebra'. In LoF all boundaries are
  considered equivalent.

  The topology of LoF implicitly imposes commutativity on its operations
  and transferring this to a linear notation involves compromises. To better
  understand the compromises and see the cost of linearity was a major
  motivation of this exercise.

  As has become standard, I use matching parentheses (...) to represent
  boundaries. And I need to explicitly state the commutative property.
  The ramifications of this last point are felt throughout the ensuing
  derivations, as properties that are obvious in the 2D notation have to be
  spelled out case by case in auxiliary theorems. The system as formulated
  is simply unable to prove general statements of commutativity.
$)

  $( constants $)
  $c ( ) = |- form $.

  $( variables $)
  $v p q r s t u v w x y $.

  $( forms $)
  tp  $f form p $.
  tq  $f form q $.
  tr  $f form r $.
  ts  $f form s $.
  tt  $f form t $.
  tu  $f form u $.
  tv  $f form v $.
  tw  $f form w $.
  tx  $f form x $.
  ty  $f form y $.

  $( Axioms ---------------------------------------------------
     In keeping with the spirit of LoF's austerity, I aimed for the most
     minimal formalism possible. I start with the five constant symbols listed
     above and seven basic axioms: three to provide a recursive definition of
     'form', three common notions (so to speak) to power symbol manipulation,
     and a commutativity axiom. Metamath does not distinguish definitions from
     proper axioms.
  $)

  $( Recursive Definition of Form -----------------------------
     1. Empty space is a form.
     2. If p is a form, enclosing it in parentheses is a form.
     3. If p and q are forms, juxtaposing them is a form.
  $)

  $( Empty space is a form. $)
  void  $a form $.

  $( If p is a form, then (p) is a form. $)
  encl  $a form ( p ) $.

  $( If p and q are forms, then p q is a form. $)
  juxt  $a form p q $.


  $( Common Notions --------------------------------------------
     One goal of lof.mm is exploring the minimal basis for a boundary algebra.
     The next 3 axioms are the required machinery of symbol manipulation.
  $)

  ${
    euc.1   $e |- p = q   $.
    euc.2   $e |- r = q   $.
    $( Two things equal to the same thing are equal to each other. This is
       Euclid's first Common Notion and, in an equational logic, this and
       its sibling, transitivity, are the main engine of derivation. $)
    ax-euc  $a |- p = r   $.
  $}

  $( Euclid's second and third Common Notions are specific to quantity,
     so not exactly common. We can rephrase them as: doing the same thing
     (e.g., applying the same operation) to equal things leaves equal things.
     Applying this to LoF's two operations, enclosure and juxtaposition,
     leads to the next two axioms (looked at differently, these can also be
     seen as substitution/replacement rules).
  $)

  ${
    beq.1   $e |- p = q $.
    $( Enclosing equal forms leaves equal forms. We can consider this a
       definition of boundary equality. $)
    ax-beq  $a |- ( p ) = ( q ) $.
  $}

  ${
    sub.1   $e |- p = q $.
    $( Juxtaposing the same form with equal forms leaves equal forms. $)
    ax-sub  $a |- p v = q v $.
  $}

  $( Commutativity of LoF --------------------------------------------
     Associativity holds despite our system lacking the means
     to even state it. $)
  ax-cmm  $a |- p q = q p $.


  $( Theorems --------------------------------------------------------
     The symbol '=' is never defined but it will turn out to obey the expected
     laws of an equivalence relation. Specifically, from the common notion
     that two things equal to the same thing are equal to each other and from
     the commutativity of LoF, we derive the reflexivity, symmetry, and
     transitivity of '='. Note that such a derivation is not possible in a
     traditional formal system without additional axioms -- it is the ability
     to reference the empty (or void) form that allows it here.
  $)

  $( '=' is reflexive. $)
  id  $p |- p = p  $=
    ( void ax-cmm ) ABC $.
    $( [6-Sep-2015] $)

  ${
    sym.1  $e |- p = q $.
    $( '=' is symmetric. $)
    sym    $p |- q = p $=
      ( id ax-euc ) BBABDCE $.
      $( [2-Sep-2015] $)
  $}

  ${
    trans.1  $e |- p = q $.
    trans.2  $e |- q = r $.
    $( '=' is transitive. $)
    trans    $p |- p = r $=
      ( sym ax-euc ) ABCDBCEFG $.
      $( [2-Sep-2015] $)
  $}

  $( The axioms and theorems so far have been transparent, succinct, and
     powerful (they embody Boolean algebra, after all), but applying them
     would be impractical without further theorems. While this is no different
     from any other formal system, here these auxiliary theorems have a
     peculiar feeling of inconsequence: they are often tiresome (and sometimes
     ugly) commutative elaborations of previous statements, whose only adhoc
     utility is to ease the derivation of particular propositions.
  $)

  ${
    eucr.1  $e |- p = q $.
    eucr.2  $e |- p = r $.
    $( A commuted - or reversed - version of ax-euc. $)
    eucr    $p |- q = r $=
      ( sym trans ) BACABDFEG $.
      $( [2-Sep-2015] $)
  $}

  ${
    subr.1  $e |- p = q $.
    $( A commuted version of ax-sub $)
    subr    $p |- u p = u q $=
      ( juxt ax-sub ax-cmm eucr ) BCEZCAEZCBEACEIJABCDFACGHBCGH $.
      $( [2-Sep-2015] $)
  $}

  $( More versions of the substitution principle. Our lack of access to the
     implicit commutativity of 2D forces us to spell out each case. $)
  ${
    subst.1  $e |- p = q $.
    subst  $p |- u p v = u q v $=
      ( juxt ax-sub subr ) ADFBDFCABDEGH $.
      $( [2-Sep-2015] $)
    substr  $p |- u p v = v q u $=
      ( juxt ax-sub ax-cmm trans subr ) CAFDFCDFBFDBFZCFADFZKCLBDFKABDEGBDHIJCK
      HI $.
      $( [2-Sep-2015] $)
    subb1  $p |- w ( u p v ) x = w ( u q v ) x $=
      ( juxt encl subst ax-beq ) CAHDHZICBHDHZIEFLMABCDGJKJ $.
      $( [2-Sep-2015] $)
    subb3  $p |- w ( u p v ) x = w ( v q u ) x  $=
      ( juxt encl substr ax-beq subst ) CAHDHZIDBHCHZIEFMNABCDGJKL $.
      $( [2-Sep-2015] $)
  $}

  ${
    rep.1  $e |- p = q $.
    rep.2  $e |- u p v = y $.
    $( Direct substitution into an equation. $)
    rep    $p |- u q v = y $=
      ( juxt subst eucr ) CAHDHCBHDHEABCDFIGJ $.
      $( [18-Sep-2015] $)
  $}

  ${
    repbx.1  $e |- p = q $.
    repbx.2  $e |- w ( u p v ) x = y $.
    $( Direct substitution into an bounded-form equation. $)
    repbx    $p |- w ( u q v ) x = y $=
      ( juxt encl subb1 eucr ) ECAJDJKJFJECBJDJKJFJGABCDEFHLIM $.
      $( [18-Sep-2015] $)
  $}

  $( This theorem allows a slightly quicker proof of lem3.3.
  ${
    repbd.1  $e |- p = q $.
    repbd.2  $e |- ( ( u p v ) ) = y $.
    @( Direct substitution into a double bounded-form equation. @)
    repbd    $p |- ( ( u q v ) ) = y $=
      ( juxt encl void subb1 ax-beq eucr ) CAHDHIZICBHDHIZIENOABCDJJFKLGM $.
      @( [3-Oct-2015] @)
  $}
  $)

  ${
    quad.1  $e |- p = q $.
    quad.2  $e |- r = s $.
    $( Double substitution of equivalent forms. $)
    quad    $p |- p r = q s $=
      ( juxt void subst trans ) ACGBCGBDGABHCEICDBHFIJ $.
      $( [2-Sep-2015] $)
  $}

  ${
    ins.1  $e |- p q = r s $.
    $( Insert the same form into two equivalent forms. $)
    ins    $p |- p v q = r v s $=
      ( juxt ax-cmm ax-sub subr trans ) AEGZBGZECGZDGZCEGZDGMEAGZBGOLQBAEHIABGC
      DGEFJKNPDECHIK $.
      $( [3-Sep-2015] $)
  $}

  $( Extended commutativity $)
  cmmx  $p  |- u p v q w = u q v p w  $=
    ( juxt ax-cmm ins subst ) ADFBFBDFAFCEABBADABGHI $.
    $( [3-Sep-2015] $)

  $( Bounded and extended commutativity $)
  cmmbx  $p |- x ( u p v q w ) y = x ( u q v p w ) y $=
    ( juxt id substr subb1 ) ADHBHBDHAHCEFGDDABDIJK $.
    $( [2-Sep-2015] $)

  ${
    quadbx.1  $e |- p = q $.
    quadbx.2  $e |- r = s $.
    $( Double substitution into a bounded and extended form. $)
    quadbx    $p |- x ( u p v r w ) y = x ( u q v s w ) y  $=
      ( juxt quad ins subb1 ) AFLCLBFLDLEGHIACBDFABCDJKMNO $.
      $( [3-Sep-2015] $)
  $}

  $( It's hard to know where to stop with auxiliary theorems. Had we choosen
     to prove the two additional statements:

    tranxb.1  $e |- p = q $.
    tranxb.2  $e |- r = q $.
    tranxb    $p |- x ( v p u ) w = w ( u r v ) x $.

    tranrxb.1  $e |- p = q $.
    tranrxb.2  $e |- p = r $.
    tranrxb    $p |- x ( v q u ) w = w ( u r v ) x $.

    we could have reduced significantly the proof of theorem c9.0. $)

  $( ==========================================================================
                              Laws of Form

  LoF can be considered a prolonged deduction from two initial 'arithmetic'
  equations [LoF, p. 12]:

  I1. Number   () () = ()
  I2. Order    (())  =

  As mentioned, one of the models of LoF is sentential logic:

  T         <=>    ()
  F         <=>
  ~p        <=>    (p)
  p V q     <=>    p q
  p & q     <=>    ((p) (q))
  p -> q    <=>    (p) q
  p <-> q   <=>    ((p) (q)) (p q)

  The algebra is self-dual. If we interchange T and F, the algebraic laws
  continue to hold, with juxtaposition now interpreted as conjunction:

  T         <=>
  F         <=>    ()
  ~p        <=>    (p)
  p V q     <=>    ((p) (q))
  p & q     <=>    p q
  p -> q    <=>    (p (q))
  p <-> q   <=>    (((p) (q)) (p q))

  In keeping with standard practice, I use the first interpretation
  (juxtaposition as disjunction). When refering to the second interpretation,
  I call it the 'dual interpretation'.

  Spencer-Brown begins with the two axioms:

  J1. Position                 ((p) p) =
  J2. Transposition            ((p r) (q r)) = ((p) (q)) r

  and deduces the following consequences [LoF, pp. 28-35]:

  C1. Reflexion                ((a)) = a
  C2. Generation               (a b) b = (a) b
  C3. Integration              () a = ()
  C4. Occultation              ((a) b) a = a
  C5. Iteration                a a = a
  C6. Extension                ((a) (b)) ((a) b) = a
  C7. Echelon                  (((a) b) c) = (a c) ((b) c)
  C8. Modified transposition   ((a) (b r) (c r)) = ((a) (b) (c)) ((a) (r))
  C9. Crosstransposition       (((b) (r)) ((a) (r)) ((x) r) ((y) r)) =
                               ((r) a b) (r x y)

  To see that J1 and J2 constitute a complete set of axioms, refer to
  chapter 9 of LoF [pp. 50-52].

  One of the goals of lof.mm was to establish different bases (initial
  axioms) for the algebra. To do this in one file, I need a way to reference
  the same theorems in the different bases. Retaining Spencer-Brown's original
  numbering scheme for cross-referencing, I label the theorems as ck.n (jk.n),
  where ck (jk) refers to LoF's Ck (Jk) and n refers to the basis under
  consideration. In other words, ck.n = ck.m  (jk.n = jk.m) for all n, m.
  LoF's system is n = 0.

  ==========================================================================

  System_0

  This version follows LoF but doesn't attempt to mimic its specific steps.
  For example, theorem C5 is derived before C4. $)

  $( Basis_0 -------------------------------------------- $)

  $( Position $)
  j1.0  $a |- ( ( p ) p ) = $.

  $( Transposition $)
  j2.0  $a |- ( ( p r ) ( q r ) ) = ( ( p ) ( q ) ) r $.

  $( System_0 consequences ------------------------------------ $)

  $( Reflexion $)
  c1.0  $p |- ( ( p ) ) = p $=
    ( encl juxt void j1.0 ax-sub sym j2.0 ax-euc cmmbx subb1 trans quadbx ) ABZ
    BZOACBZNACBZCBZAOAOCBZBZROONCBZSCBZTONOCBZSCBZUBOUAOCZUDUEOUADONEZFGNAOHIUC
    UADSDDNODDDDDJKLUADDSDDUFKLSPDQDDDDDAODDDDDJQDAEGMLROBOCBZACAONAHUGDAOEFLL
    $.
    $( [6-Sep-2015] $)

  $( Generation $)
  c2.0  $p |- ( p q ) q = ( p ) q $=
    ( encl juxt j2.0 void c1.0 quadbx trans j1.0 subb1 eucr ) ACZBDZCZBCZBDCZDC
    ZABDCBDZNRMCZPCZDCBDSMPBETAUABFFFFBAGBGHIROCNQFOFFFBJKNGIL $.
    $( [6-Sep-2015] $)

  $( Integration $)
  c3.0  $p |- ( ) p  = ( ) $=
    ( encl juxt void c2.0 c1.0 j1.0 ax-beq eucr ) ABACZDBZACKDAEJBZBJKJFLDAGHII
    $.
    $( [6-Sep-2015] $)

  $( Iteration $)
  c5.0  $p |- p p = p $=
    ( encl juxt c2.0 void c1.0 subst trans j1.0 eucr ) ABZACBZACZAACZAMKBZACNKA
    DOAEAAFGHLEEAAIGJ $.
    $( [6-Sep-2015] $)

  $( Occultation $)
  c4.0  $p |- ( ( p ) q ) p = p $=
    ( encl juxt void j2.0 c1.0 subb1 trans c5.0 eucr c3.0 subst ) ACZBDCADZECZC
    ZADZAOPBCZCZDZCADZRONSADCZDCZUBAADZCZUCDCZOUDUGNTDCADOASAFTBNEEABGHIUFNEUCE
    EUEAEEEEAJHHKESAFIUAPEEEATLHIQEEAEGMI $.
    $( [6-Sep-2015] $)

  $( Extension $)
  c6.0  $p |- ( ( p ) ( q ) ) ( ( p ) q ) = p  $=
    ( encl juxt c1.0 void cmmbx quadbx j2.0 trans ax-beq j1.0 subb1 eucr ) ACZB
    CZDCZOBDCZDZOCZASCZCZSTSEUBPCPDCZODZCTUAUDUAPODCZBODCZDCUDQUERUFFFFFFOPFFFF
    FGOBFFFFFGHPBOIJKUCFFOFFPLMJNAEJ $.
    $( [6-Sep-2015] $)

  $( Echelon $)
  c7.0  $p |- ( ( ( p ) q ) r ) = ( p r ) ( ( q ) r ) $=
    ( juxt encl j2.0 ax-beq void c1.0 subb1 trans eucr ) ACDEBEZCDEDZEZEZAEZBDE
    CDZEZNPQMEZDECDZESOUAAMCFGUARTBQHHCBIJGKNIL $.
    $( [6-Sep-2015] $)

  $( Modified transposition $)
  c8.0  $p |- ( ( p ) ( q s ) ( r s ) ) =
              ( ( p ) ( q ) ( r ) ) ( ( p ) ( s ) ) $=
    ( encl juxt void c1.0 j2.0 ax-beq subb3 repbx c7.0 cmmbx quad trans ) AEZBD
    FEZFCDFEZFEBEZCEZFZEDFZEZQFEZQTFUAFEZQDEZFEZFZRSFZEZEZUJQGGGUEUJHULUDQGGGUK
    UCBCDIJKLUEUBQFEZUGQFEZFUIUBDQMUMUFUNUHUBQGGGGGNUGQGGGGGNOPP $.
    $( [6-Sep-2015] $)

  $( Crosstransposition $)
  c9.0  $p |- ( ( ( q ) ( p ) ) ( ( r ) ( p ) ) ( ( s ) p ) ( ( t ) p ) ) =
              ( ( p ) q r ) ( p s t )  $=
    ( encl juxt c1.0 j2.0 quadbx trans eucr subb3 c8.0 subb1 c2.0 cmmbx void
    ax-beq c6.0 ) BFZAFZGFZCFZUBGFZGZDFZAGFZGEFZAGFZGFDEGZFZAGZFZUCGUEGFZUBBGCG
    FZADGEGFZGZUHUJGZUNUFRRRUSFZFUSUNUSHUTUMUTUGFZUIFZGFAGUMUGUIAIVADVBERRRRADH
    EHJKSLMUOUNBGCGZFZUKAGFZGZURUOVDULFZAGZFGZVFUOVDUNAGZFGZVIUOVDUNUBFZGFZGZVK
    UOUNUAFZGUDFZGFVMGVNUMUAUDUBNVOBVPCUNRRRVMBHCHJKVLAUNRVDRAHZOKVJVHRRVDRULAP
    OKVGUKRAVDRUKHOKVCVEGFVEGZVFURVCVEPVRAULGFZBGCGZUQGFVEGZURUNVSVEUQRBCGZRRVE
    ULARRRRRQUKARRRRRQJVLULGFZBGCGZVLDGEGFZGFVEGZWAURWDVTWEUQRRRRVEVLARULRWBVQO
    VLARUKRRVQOJWFWCWEGZBGCGFVEGZURWBWEWCRRRVEQWHUPVEGURWGUBRWBRVEUBUKTOUKARRRU
    PRQKKLKLKK $.
    $( [6-Sep-2015] $)

  $( =======================================================================

     System_1

     Although System_0 is the only one demonstrated by Spencer-Brown, and so
     can be considered canonical, he mentions in his notes an alternate basis
     of C5 and C6, but suggests the derivation is 'both difficult and tedious'
     [LoF, p.89]. Readers can decide for themselves whether System_1 is any
     more complicated than System_0. The virtue of this basis, as noted by
     Spencer-Brown, is the need for only two distinct variables.

     The derivation below ends at the point where both j1.1 and j2.1 are
     proved, since that establishes c5.1 and c6.1 as a complete basis. $)

  $( Basis_1 --------------------------------------------- $)

  c5.1  $a |- p p = p $.
  c6.1  $a |- ( ( p ) ( q ) ) ( ( p ) q ) = p $.

  $( System_1 consequences ------------------------------------ $)

  $( Lemma for proof of c1.1. Under the dual interpretation, this is mildly
     reminiscent of modus ponens: (p & (p -> q)) <-> (p & q). $)
  lem1.1  $p |- p ( ( q ) p ) = p q $=
    ( encl juxt void cmmbx subst cmmx trans c5.1 ax-sub c6.1 quad eucr ) ACZBCZ
    DCZOBDCZDZPODCZPADCZDZDZAUADZABDUCSUADZUDUCQQDZRUADZDZUEUCSQUADDUHTQSUAPOEE
    EEEFGRQQEUAHIUFQUGQJKISAUAABLZKISAUBBUIBALMN $.
    $( [17-Sep-2015] $)

  c1.1  $p |- ( ( p ) ) = p $=
    ( void lem1.1 ) BAC $.
    $( [17-Sep-2015] $)

  $( The LoF I2 arithmetic initial. This is also directly derivable from the
     basis by plugging void values into c6.1, followed by two applications of
     c5.1. $)
  i2.1  $p |- ( ( ) ) = $=
    ( void c1.1 ) AB $.
    $( [17-Sep-2015] $)

  $( One of the two equations from Basis_0. $)
  j1.1  $p |- ( ( p ) p ) = $=
    ( encl juxt void c1.1 subr ax-cmm i2.1 subb1 quad c6.1 eucr ax-beq trans )
    ABZACZBDBZBZDPQOOBZCZPQSAOAEFSOCZTQSOGROCBZRACBZCUAQUBSUCORDDODDHIRDDADDHIJ
    QAKLLLMHN $.
    $( [17-Sep-2015] $)

  c4.1  $p |- ( ( p ) q ) p = p $=
    ( encl juxt void c6.1 substr c5.1 subr eucr trans ) ACZBDCZADZLBCDCZMDZAPMD
    NPPAEMABFZGMMDMOMHIJQK $.
    $( [18-Sep-2015] $)

  $( Corollary of c4.1 $)
  c4cor.1  $p |- ( p  q ) ( p ) = ( p ) $=
    ( encl juxt void c1.1 subb1 c4.1 eucr ) ACZCZBDCJDABDCJDJKAEBEJAFGJBHI $.
    $( [18-Sep-2015] $)

  $( Corollary of c6.1 $)
  c6cor.1  $p |- ( ( p ) q ) ( p  q ) = ( q ) $=
    ( juxt void encl ax-cmm c1.1 c6.1 repbx ) BACZABCDDAEZBCZEDBEZBAFBKCZLDDDJE
    MBKFMEZBDANEDMBGZOBDKDOACEMPMAHIIII $.
    $( [22-Sep-2015] $)

  c7.1  $p |- ( ( ( p ) q ) r ) = ( p r ) ( ( q ) r )  $=
    ( juxt encl void ax-cmm c4cor.1 c6cor.1 c4.1 c1.1 c6.1 repbx eucr quad c5.1
    cmmbx trans rep sym ) ACDZEZBEZCDZEDAEZBDEZCDZEZCUCDZUDFFUBFUHCUCGCADZUAFFF
    UIEZUHCAGUIUEDZEUKDUKUJEZFUHUIUEHUECDZUCDZULFFUMUKUHUEUIGUKUMUOEZDZDUQUKDFF
    UHUKUQGUJBDEZUMDUMUKUPUHUJBHUKURDZUMDUPDUHUHDUHUSUHUQUHUFABDZEZDUCCFFURUHAB
    IUGCUFDZFVAFURUHUFCGZUFADACBUGVADEZFUHABJUGVBFUTVDFUHVCUHEZUGFUTVDFUHUGKZVE
    UGFVAFVEUTDEUHVFUHUTLMMMMMMBUEDEZUCDUCUNFUMFUHBUEHUNUFDUCDZUNVGDUCDFFUMFUHU
    EBFFFUNUCQUMUGUEDUCDEZDUMVHEDUHUFUEFCUCUMFQUEUCDZEZUFDZACFFVIUHABLUFVKDVLCF
    FVIUHUFVKGUGVBFVKFVIUHVCVEUGFVJUGVKDEFUHVFVEUGFVKFVEVJDEUHVFUHVJLMMMMMNMMOU
    HPRSSMSMMT $.
    $( [23-Sep-2015] $)

  $( The second of the two equations from Basis_0. This completes the proof
     that Basis_1 is at least as powerful as Basis_0. $)
  j2.1  $p |- ( ( p ) ( q ) ) r = ( ( p r ) ( q r ) ) $=
    ( encl juxt c1.1 c7.1 void subb1 trans ax-beq eucr ) ADBDZEDCEZDZDNACEDZBCE
    DEZDNFOQOPMDZCEDEQAMCGRBHCPHBFIJKL $.
    $( [23-Sep-2015] $)

$( =======================================================================

     System_2

     Having shown that C5 and C6 form a basis, I now show that C6 alone
     suffices. The derivation ends at the point where c5.2 is proved, since
     that establishes that Basis_2 is at least as powerful as Basis_1. $)

  $( Basis_2 --------------------------------------------- $)

  c6.2  $a |- ( ( p ) ( q ) ) ( ( p ) q ) = p $.

  $( System_2 consequences ------------------------------------ $)

  $( An important lemma used in the proof of c1.2. $)
  lem2.2  $p |- ( p ) p = ( q ) q $=
    ( encl juxt void c6.2 ax-cmm quad subb1 eucr subst trans cmmx sym rep repbx
    ax-beq ) BCZBDACZADZRSCZDZCZRSDZCDBRETBSFSRDZUDEERUCDETSRGUARDZUBEERUECZTUA
    RGRCZUADZCZUHSDZCZDZREUFCZUGDTRSFTUMUNDUGDZTUJUNDZULDUGDUOTUPSUHDZCZUGDZDZU
    PULUGDDUAUHDZCUNDZUSDTUTVBSUSASRFARFHVAUIEEEUNURDUGDUAUHGIJURULUPUGUQUKSUHG
    QKLUNULUJEUGMLNOPPON $.
    $( [24-Sep-2015] $)

  $( This is axiom B3 from Meguire. $)
  b3.2  $p |- ( p ) p = ( ) $=
    ( void lem2.2 ) ABC $.
    $( [18-Aug-2016] $)

  c1.2  $p |-  ( ( p ) ) = p $=
    ( encl juxt void ax-cmm lem2.2 c6.2 repbx rep eucr ) ABZKBZBZCZBZKLCZBCLALK
    CZPDDODLLKEMKCZNDDDQBZLMKESRBZCTSCDDLSTEMLCQDDDTLLKFLKGHIHHALGJ $.
    $( [25-Sep-2015] $)

  j1.2  $p |- ( ( p ) p ) = $=
    ( encl juxt void b3.2 ax-beq c1.2 trans ) ABACZBDBZBDIJAEFDGH $.
    $( [25-Sep-2015] $)

  lem3.2  $p |- ( p  p ) = ( ( ( p ) ) ( ( p ) ) ) $=
    ( encl juxt void c1.2 sym id repbx ) ABBZICBAACBZAIIDDDJIAAEFZAIDADDJKJGHHF
    $.
    $( [25-Sep-2015] $)

  c5.2  $p |- p p = p $=
    ( encl juxt void c6.2 lem3.2 j1.2 sym c1.2 repbx eucr ) ABZBZAACZAMMCBZMLCB
    ZCLDDDDNLLENBZODPDDNAFDPQDDDNPDLGHNIJJJAIK $.
    $( [25-Sep-2015] $)

  $( =======================================================================

     System_3

     Deriving C6 from the Robbins equation, demonstrating that a Robbins
     algebra is a Boolean algebra. $)

  $( Basis_3 --------------------------------------------- $)

  $( The more familiar form of the Robbins equation is
     ((p q) (p (q))) = p, but for this exercise I'll be using the
     equivalent form: $)
  robbins  $a |- ( ( ( p ) q ) ( p q ) ) = q $.

  $( System_3 consequences ------------------------------------ $)

  j1.3  $p |- ( ( p ) p ) = $=
    ( tq encl juxt void robbins sym ax-beq quad trans ) ACZADZCBCADCBADCDZCZCZN
    DZCELPKOANANNABAFGZHQIHMEFJ $.
    $( [8-Dec-2016] $)

  c1.3  $p |- ( ( p ) ) = p $=
    ( encl juxt void ax-cmm ax-beq robbins repbx rep j1.3 eucr ) ABZBZACZBZBZMA
    AMCZBZBPDDMROQNAMEFFMLCZBZDDRDDMADGLMCZBTDRDDMUASLMEFAMGHHILACBDODDDAAJLAGH
    K $.
    $( [8-Dec-2016] $)

  $( Original proof by Naip Moro. $)
  c6.3orig  $p |- ( ( p ) ( q ) ) ( ( p ) q ) = p $=
    ( encl juxt void ax-cmm c1.3 robbins ax-beq eucr trans repbx ) BACZDZMBDEEM
    BCZDZCEABMFOMDZPEEENCZAOMFQCRDZMCZASCZCSTSGUAMBMHIJAGKLL $.
    $( [5-Oct-2015] $)

  $( This is a conceptually simpler proof suggested by Armahedi Mahzar. $)
  c6.3  $p |- ( ( p ) ( q ) ) ( ( p ) q ) = p $=
    ( encl juxt void cmmbx c1.3 robbins ax-beq trans eucr ) ACZBCZDCZBLDCZDZNLB
    DCDABLEEENEFMLDCODZPAMLEEEEOFQCZCZQAQGSLCARLBLHIAGJKKK $.
    $( [27-Jan-2017] $)

  $( =======================================================================
                         Topics in Laws of Form

  Associativity of logical connectives

  Since LoF lacks the concept of associativity, proving that a model
  of LoF has associative connectives may involve meta-reasoning. For
  example, the proof of (p V q) V r = p V (q V r) corresponds to the
  equation p q r = p q r, which is easy to prove in LoF! Under the dual
  interpretation this also proves the associativity of conjunction, but
  here I will prove that more directly. Since p & q corresponds to
  ((p)(q)), we need to show that ((((p)(q))) (r)) = ((p) (((q)(r)))).
  Consider the left side of that equation -- it evaluates to ((p)(q)(r)),
  a form symmetric in the three variables: $)

  conj3  $p |- ( ( ( ( p ) ( q ) ) ) ( r ) ) = ( ( p ) ( q ) ( r ) ) $=
    ( encl juxt void c1.0 subb1 ) ADBDEZDDIFCDFFIGH $.
    $( [29-Dec-2016] $)

  $( This shows that a permutation of variables in the LHS leaves the
  result unchanged. Specifically, ((((q)(r))) (p)), which is equal to
  ((p) (((q)(r)))) by commutation, will evaluate to the same form as
  ((((p)(q))) (r)). This completes the proof. I call this meta-reasoning
  because we're using an undefined, intuitive notion of symmetry. Below
  is the full-length formal proof. $)

  $( Associativity of conjunction $)
  conj-assc $p |- ( ( ( ( p ) ( q ) ) ) ( r ) ) = ( ( p ) ( ( ( q ) ( r ) ) ) )
            $=
    ( encl juxt conj3 void ax-cmm subb1 trans ax-euc ax-beq ) ADZBDZEZDDCDZEDZN
    PEZDDZMEZDZMSEZDQOPEZDZUAABCFUARMEZDUDBCAFUEUCGGGGRMHIJKTUBSMHLJ $.
    $( [29-Dec-2016] $)

  $( Now I turn to proving the associativity of the biconditional:
  (p<->q)<->r = p<->(q<->r). I had earlier taken for granted that p<->q,
  transcribed as (((p)q) ((q)p)), was equivalent to ((p)(q)) (p q). Here
  I prove it: $)

  bicond  $p |- ( ( ( p ) q ) ( ( q ) p ) ) = ( ( p ) ( q ) ) ( p q ) $=
    ( encl juxt void ax-cmm ax-beq subb1 c1.0 c6.0 cmmbx c9.0 eucr ) BACZDZCZBC
    ZADCZDZCZNBDZCZRDCNQDCABDCDZPUBEREEOUABNFGHQCZNDCZRDZCZTUCUFSUDBENERBIHGECZ
    NDCZUHADCZDZUEDRDCZUGUCUKEEUFEEEAJHUIUEDRDUJDCULUCUFUJUIEEEEKAEQBELMMMM $.
    $( [29-Dec-2016] $)

  $( Next I'll need the following two lemmas: $)

  c2lem1  $p |- ( q ( p q ) r ) = ( ( p ) q r ) $=
    ( juxt encl void cmmx c2.0 ax-sub trans ax-beq ) BABDEZDCDZAEBDZCDZMLBDZCDO
    BLFFCGPNCABHIJK $.
    $( [29-Dec-2016] $)

  c2lem2  $p |- ( p ( p q ) r ) = ( p ( q ) r ) $=
    ( juxt encl void cmmbx cmmx trans c2.0 ax-sub ax-beq ) AABDEDCDZABEZDCDZMNA
    DZCDZOMBADEZADZCDZQMARDCDTABFFFACGARFFCHISPCBAJKINAFFCHIL $.
    $( [29-Dec-2016] $)

  $( Let A = p<->q = ((p)(q)) (p q) and
         B = q<->r = ((q)(r)) (q r).
  Proving that the biconditional associates amounts to proving:
      ((A)(r)) (A r) = ((p)(B)) (p B), i.e.,
      ((((p)(q)) (p q))(r)) (((p)(q)) (p q) r) =
      ((p)(((q)(r)) (q r))) (p ((q)(r)) (q r)).
  Consider the left side of that equation -- as in the case of conjunction,
  it evaluates to a form symmetric in the three variables: $)

  bic3  $p |-
      ( ( ( ( p ) ( q ) ) ( p q ) ) ( r ) ) ( ( ( p ) ( q ) ) ( p q ) r ) =
      ( ( p ) ( q ) ( r ) ) ( p q ( r ) ) ( p ( q ) r ) ( ( p ) q r ) $=
    ( encl juxt j2.0 ax-beq c1.0 eucr quad c2lem2 subst trans c2lem1 subr ) ADZ
    BDZEZDABEZDZEZDCDZEZDZUACEZDZEZRUBEDSUBEDEZAQECEDZEZBTECEDZEUJPBECEDZEUGUHA
    TECEDZUKEZEUHUIUKEEUDUHUFUNUHDZDUDUHUOUCRSUBFGUHHIUNDZDUFUNUPUEABTCEFGUNHIJ
    UMUIUHUKABCKLMUKULUJABCNOM $.
    $( [29-Dec-2016] $)

  $( This completes the informal proof that the biconditional associates.
  Below is the formal proof. First, we need a permuted version of bic3. $)

  bic3x  $p |-
      ( ( ( ( q ) ( r ) ) ( q r ) ) ( p ) ) ( ( ( q ) ( r ) ) ( q r ) p ) =
      ( ( p ) ( q ) ( r ) ) ( p q ( r ) ) ( p ( q ) r ) ( ( p ) q r ) $=
    ( encl juxt bic3 void cmmbx trans cmmx ) BDZCDZEZDBCEZDEZDADZEDOAEDEZPKELED
    ZPBECEDZEZAKECEDZEABELEDZEZRUBEUAESEQTUBEZUAEZUCQUDKCEZAEDZEZUEQTBLEZAEDZEU
    GEZUHQRNPEDZEUJEUGEZUKQMPEDULEUJEUGEUMBCAFMPGGGGULUJEUGEHINPGGGRUJUGEHIUIAG
    GGTUGHIUFAGGGUDGHIUBUATGGJISUBRUAGJI $.
    $( [29-Dec-2016] $)

  $( The associativity of the biconditional $)
  bicond-assc  $p |-
      ( ( ( ( p ) ( q ) ) ( p q ) ) ( r ) ) ( ( ( p ) ( q ) ) ( p q ) r ) =
      ( ( p ) ( ( ( q ) ( r ) ) ( q r ) ) ) ( p ( ( q ) ( r ) ) ( q r ) ) $=
    ( encl juxt bic3 bic3x ax-euc void cmmbx trans ) ADZBDZEZDABEZDEZDCDZEDPCED
    EZMQEDZBCEDZEZDZLEDUAAEDZEZLUBEDZASETEDEZRNQEDOQEDEAMECEDELBECEDEUDABCFABCG
    HUDUEUCEUFUBLIIIIUCJUAAIIIUEIJKK $.
    $( [29-Dec-2016] $)


$( 
  lof.mm    version 0.1.0    Copyright (C) 2015 naipmoro
  This file is made available under the MIT License: 
  http://opensource.org/licenses/MIT

  lof.mm presents metamath derivations of the Primary Algebra from
  Spencer-Brown, G. (1969) Laws of Form (Allen & Unwin, London),
  hereafter cited as LoF. Spencer-Brown will be cited as SB.

  The algebra of LoF has a number of models, most significantly Boolean 
  algebra and sentential logic, so it may be of some interest to logicians. 
  From the perspective of metamath, it is a non-trivial example of a system 
  that requires, indeed is based on, the empty substitution.

  LoF is a 2D topological notation in which closed curves (boundaries) are the
  symbols under investigation, and in which the only properties of interest
  are whether a given boundary is inside or outside of another boundary,
  intersecting boundaries not being allowed. Variables p q r ... will range 
  over possible arrangements of boundaries (which we call 'forms'). It is now 
  common to call LoF a 'boundary algebra'. 

  Given the topological nature of the system, its operations are implicitly
  commutative. Transferring this to a linear notation involves compromises. 
  As has become standard, I use matching parentheses (...) to represent 
  boundaries. And I will need to explicitly state the commutative property. 
  The ramifications of this last point are felt throughout the ensuing 
  derivations, as properties that are obvious in the 2D notation have to be 
  spelled out case by case in auxiliary theorems.  
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

  $( Inductive Definition of Form -----------------------------
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


  $( Common Axioms --------------------------------------------   
     One goal of lof.mm is exploring the minimal basis for a boundary algebra.
     The next 4 axioms are the required machinery of symbol manipulation. 
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
     seen as substitution/replacement rules). $)
  
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
 
  $( Commutativity of LoF. $)
  ax-cmm  $a |- p q = q p $.
  
 
  $( Consequences from the common axioms ----------------------

     The symbol '=' is never defined but it will turn out to obey the expected
     laws of an equivalence relation. Specifically, from the common notion 
     that two things equal to the same thing are equal to each other and from 
     the commutativity of LoF, we derive the reflexivity, symmetry, and 
     transitivity of '='. Note that such a derivation is not possible in a
     traditional formal system without additional axioms -- it is the ability 
     to reference the empty (or void) form that allows it here. $)

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
 
  $( Now a series of auxiliary theorems. $)
  
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
    $( Direct substitution into an bounded form. $)
    repbx    $p |- w ( u q v ) x = y $= 
      ( juxt encl subb1 eucr ) ECAJDJKJFJECBJDJKJFJGABCDEFHLIM $.
      $( [18-Sep-2015] $)
  $}

  ${
    repb2.1  $e |- p = q $.
    repb2.2  $e |- ( ( u p v ) ) = y $.
    $( Direct substitution into a double-bounded-form. $)
    repb2    $p |- ( ( u q v ) ) = y $= 
      ( juxt encl void subb1 ax-beq eucr ) CAHDHIZICBHDHIZIENOABCDJJFKLGM $.
      $( [3-Oct-2015] $)

     
  $}

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
    tp tv juxt tq juxt tq tv juxt tp juxt tu tw
    tp tq tq tp tv
    tp tq ax-cmm  
    ins
    subst $.

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

  $( It's hard to know where to stop with auxiliary theorems. If we choose 
     to prove the two additional statements:
         $p |- x ( v p u ) w = w ( u r v ) x $.
         $p |- x ( v q u ) w = w ( u r v ) x $.
     we can reduce the proof of c9.0 by a hundred steps. $)

  $( ==========================================================================
                              Laws of Form  
  
  The 'arithmetic' of LoF consists of two equations [LoF, p. 12]:

  I1. Number   () () = ()
  I2. Order    (())  =   
  
  As mentioned, one of the models of LoF is sentential logic:
   
  T             <=>    ()
  F             <=>     
  NOT p         <=>    (p)
  p OR q        <=>    p q   
  p AND q       <=>    ((p) (q))   
  p IMPLIES q   <=>    (p) q
  p IFF q       <=>    ((p) (q)) (p q)
  
  The algebra is self-dual. If we interchange T and F, the algebraic laws 
  continue to hold, with juxtaposition now interpreted as conjunction:

  T             <=>    
  F             <=>    ()
  NOT p         <=>    (p)
  p OR q        <=>    ((p) (q))
  p AND q       <=>    p q
  p IMPLIES q   <=>    (p (q))
  p IFF q       <=>    (((p) (q)) (p q))  

  Unless otherwise noted, I use the first interpretation (juxtaposition as
  disjunction). When refering to the second interpretation, I call it the
  'dual interpretation' or just the 'dual'. Spencer-Brown begins with the 
  axioms:

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

  One of the goals of lof.mm is establishing different bases (initial 
  axioms) for the algebra. Since I aim to do this in one file, I need
  a way to reference the same theorems in the different bases. Retaining
  Spencer-Brown's original numbering scheme for cross-referencing, I label 
  the theorems as ck.n (jk.n), where ck (jk) refers to LoF's Ck (Jk) and
  n refers to the basis under consideration. In other words, ck.n = ck.m 
  (jk.n = jk.m) for all n, m. LoF's system is n = 0.

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
  c1.0  $p |- ( ( p ) ) =  p $=
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
    ( encl juxt c1.0 void cmmbx quadbx j2.0 trans ax-beq j1.0 subb1 eucr) ACZBC
    ZDCZOBDCZDZOCZASCZCZSTSEUBPCPDCZODZCTUAUDUAPODCZBODCZDCUDQUERUFFFFFFOPFFFFF
    GOBFFFFFGHPBOIJKUCFFOFFPLMJNAEJ $.
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

     Although System_0 is the only one demonstrated by SB, and so can be
     considered canonical, he mentions in his notes an alternate basis of 
     C5 and C6, but suggests the derivation is 'both difficult and tedious' 
     [LoF, p.89]. Readers can decide for themselves whether System_1 is any 
     more complicated than System_0. The virtue of this basis, as noted by SB, 
     is the need for only two distinct variables. 

     The derivation below ends at the point where both j1.1 and j2.1 are 
     proved, since that establishes c5.1 and c6.1 as a legitimate basis. $)
  
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
     that Basis_1 is at least equivalent to Basis_0. $)
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
  lem1.2  $p |- ( p ) p = ( q ) q $=
    ( encl juxt void c6.2 ax-cmm quad subb1 eucr subst trans cmmx sym rep repbx
    ax-beq ) BCZBDACZADZRSCZDZCZRSDZCDBRETBSFSRDZUDEERUCDETSRGUARDZUBEERUECZTUA
    RGRCZUADZCZUHSDZCZDZREUFCZUGDTRSFTUMUNDUGDZTUJUNDZULDUGDUOTUPSUHDZCZUGDZDZU
    PULUGDDUAUHDZCUNDZUSDTUTVBSUSASRFARFHVAUIEEEUNURDUGDUAUHGIJURULUPUGUQUKSUHG
    QKLUNULUJEUGMLNOPPON $.
    $( [24-Sep-2015] $)

  $( This is Meguire's axiom B3. $)
  b3.2  $p |- ( p ) p = ( ) $=
    tp void lem1.2
    $.

  c1.2  $p |-  ( ( p ) ) = p $= 
    ( encl juxt void ax-cmm lem1.2 c6.2 repbx rep eucr ) ABZKBZBZCZBZKLCZBCLALK
    CZPDDODLLKEMKCZNDDDQBZLMKESRBZCTSCDDLSTEMLCQDDDTLLKFLKGHIHHALGJ $.
    $( [25-Sep-2015] $)

  j1.2  $p |- ( ( p ) p ) = $=
    ( encl juxt void b3.2 ax-beq c1.2 trans ) ABACZBDBZBDIJAEFDGH $.
    $( [25-Sep-2015] $)

  lem2.2  $p |- ( p  p ) = ( ( ( p ) ) ( ( p ) ) ) $=
    ( encl juxt void c1.2 sym id repbx ) ABBZICBAACBZAIIDDDJIAAEFZAIDADDJKJGHHF
    $.
    $( [25-Sep-2015] $)

  c5.2  $p |- p p = p $=
    ( encl juxt void c6.2 lem2.2 j1.2 sym c1.2 repbx eucr ) ABZBZAACZAMMCBZMLCB
    ZCLDDDDNLLENBZODPDDNAFDPQDDDNPDLGHNIJJJAIK $.
    $( [25-Sep-2015] $)

  $( ======================================================================= 

     System_3  

     Investigating the Robbins algebra. $)

  $( Basis_3 --------------------------------------------- $)

  robbins  $a |- ( ( ( p ) q ) ( p q ) ) = q $.

  $( System_3 consequences ------------------------------------ $)

  lem1.3  $p |- ( ( ( p ) ) ( p ) ) =  $=
    ( void robbins ) ABC $.
    $( [30-Sep-2015] $)

  lem2.3  $p |- ( ( ( p ) ( p ) ) ) = ( p ) $=
    ( encl juxt void lem1.3 robbins repbx ) ABZBHCBDDHHCBDDHAEHHFG $.
    $( [30-Sep-2015] $)

  lem3.3  $p |- ( ( ( p ) q ) ( p q ) ) = ( ( ( p ) ) ( p ) ) q $= 
    ( encl juxt robbins void lem1.3 ax-sub ax-euc ) ACZBDCABDCDCBJCJDCZBDABEKFB
    AGHI $.
    $( [30-Sep-2015] $)

  lem4.3  $p |- ( ( ( p ) ) ( p ) ) = ( ( ( q ) ) ( q ) ) $=
    ( encl juxt void lem1.3 ax-euc ) ACZCHDCEBCZCIDCAFBFG $.
    $( [1-Oct-2015] $)

  lem5.3  $p |- ( ( ( ( p ) ) ( ( p ) ) ) ) = ( ( p ) ) $= 
    ( encl juxt void lem1.3 ax-cmm ax-beq robbins repbx ) ABZBZJCZBZDKKCBZDDDKA
    EJKCZBMNDDDKOLJKFGJKHII $.
    $( [2-Oct-2015] $)

  lem6.3  $p |- ( ( ( ( p ) )  p ) ) = ( ( p ) ) $= 
    ( encl juxt void ax-cmm ax-beq lem1.3 robbins repbx rep ) AABZBZCZBZBLACZBZ
    BDDLNPMOALEFFLKCZBZDDNDDLAGKLCZBRDNDDLSQKLEFALHIIJ $.
    $( [2-Oct-2015] $)

  lem7.3  $p |- ( ( ( ( p ) ) ( p ) ) ) = ( ) $=
    ( encl juxt void lem1.3 ax-beq ) ABZBGCBDAEF $.
    $( [2-Oct-2015] $)

  lem8.3  $p |- ( ( ( ) ( ( p ) ) ( p ) ) ) = ( ) $=
    ( encl juxt void lem7.3 ax-sub ax-beq lem6.3 trans eucr ) ABZBZKCZBBZMCZBZB
    DBZLCKCZBZBQPSORNQMAEZFGGNLCKCBBNQMHTIJ $.
    $( [3-Oct-2015] $)


  lem9.3  $p |- ( ( ( ) ) ) = ( )  $= 
    ( void encl juxt lem8.3 lem1.3 lem3.3 repbx ax-beq sym lem7.3 repb2 trans
    tp ) ABZMBZBZCOCBZBZNAANMDRBZBNBNCBZPCOCZBZBNSUBRUAPOCZBAQAAAUAMEAUCFGHHATA
    UCNTAAEIMJKLK $.
    $( [3-Oct-2015] $)


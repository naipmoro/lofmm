$( 
  lof.mm    version 0.1.0    Copyright (c) 2015 naipmoro
  This file is made available under the MIT License: 
  http://opensource.org/licenses/MIT

  lof.mm presents metamath derivations of the Primary Algebra from
  Spencer-Brown, G. (1969) Laws of Form (Allen & Unwin, London),
  hereafter cited as LoF.

  The algebra of LoF has a number of models, most significantly Boolean 
  algebra, equational logic, and the propositional calculus, so it may be of 
  some interest to logicians. From the perspective of metamath, it is a 
  non-trivial example of a system that requires, indeed is based on, the empty 
  substitution.

  LoF is a 2D topological notation in which closed curves (boundaries) are the
  symbols under investigation, and in which the only properties of interest
  are whether a given boundary is inside or outside of another boundary,
  intersecting boundaries not being allowed. Variables p q r ... will range 
  over possible arrangements of boundaries (which we call 'forms'). It is now 
  common to call LoF a 'boundary algebra'. 

  Given the topological nature of the system, the operations are implicitly
  commutative. Transferring this to a linear notation involves compromises. 
  As has become standard, we use matching parentheses (...) to represent 
  boundaries. And we will need to explicitly state the commutative property. 
  The ramifications of this last point are felt throughout the derivations, 
  as properties that are obvious in the 2D notation have to be spelled out 
  case by case in auxiliary theorems.  
$)

  $( constants $)
  $c ( ) = |- form $.

  $( variables $)
  $v p q r s t u v w x y $.

  $( forms $)
  tp $f form p $.
  tq $f form q $.
  tr $f form r $.
  ts $f form s $.
  tt $f form t $.
  tu $f form u $.
  tv $f form v $.
  tw $f form w $.
  tx $f form x $.
  ty $f form y $.

  $( ----------- Recursive Definition of Form ------------

     1. Empty space is a form.
     2. If p is a form, enclosing it in parentheses is a form. 
     3. If p and q are forms, juxtaposing them is a form. 
  $)
    
  void  $a form $.         $( Empty space is a form. $)
  encl  $a form ( p ) $.   $( If p is a form, then (p) is a form. $)
  juxt  $a form p q $.     $( If p and q are forms, then p q is a form. $)


  $( --------------- Common Axioms ---------------- 
     
     We require the next 4 axioms for the machinery of symbol manipulation. $)
   
    
  ${  
    euc.1      $e |- p = q   $.
    euc.2      $e |- r = q   $.
    $( Two things equal to the same thing are equal to each other. This is
       Euclid's first Common Notion and, in an equational logic, this and 
       its sibling (transitivity) are the main engine of derivation. $)
    ax-euc     $a |- p = r   $.  
  $}
   
  $( Euclid's second and third Common Notions are specific to quantity, 
     so not exactly common. We can rephrase them as: doing the same thing 
     (e.g., applying the same operation) to equal things leaves equal things. 
     Applying this to LoF's two operations, enclosure and juxtaposition,
     leads to the next two axioms (looked at differently, these can also be
     seen as substitution/replacement rules). $)
  
  ${  
    beq.1      $e |- p = q $.
    $( Enclosing equal forms leaves equal forms. We can consider this a 
       definition of boundary equality. $)
    ax-beq     $a |- ( p ) = ( q ) $.  
  $}

  ${  
    sub.1      $e |- p = q $.
    $( Juxtaposing the same form with equal forms leaves equal forms. $)
    ax-sub     $a |- p r = q r $.  
  $}
 
  $( Commutativity of LoF. $)
  ax-cmm     $a |- p q = q p $.
  
 
  $(    =========== Consequences from the common axioms =============

     We never define the symbol '=' but it will turn out to obey the expected
     laws of an equivalence relation. Specifically, from the common notion 
     that two things equal to the same thing are equal to each other and from 
     the commutativity of LoF, we derive the reflexivity, symmetry, and 
     transitivity of '='. Note that such a derivation is not possible in a
     traditional formal system without additional axioms -- it is the ability 
     to reference the empty (or void) form that allows it here. $)

  $( '=' is reflexive. $)
  id         $p |- p = p  $=
    ( void ax-cmm ) ABC $.
    $( [6-Sep-2015] $)
 
  ${  
    $( '=' is symmetric. $)
    sym.1      $e |- p = q $.
    sym        $p |- q = p $=
      ( id ax-euc ) BBABDCE $.
      $( [2-Sep-2015] $)
  $}
 
  ${  
    $( '=' is transitive. $)
    trans.1    $e |- p = q $.
    trans.2    $e |- q = r $.
    trans      $p |- p = r $=
      ( sym ax-euc ) ABCDBCEFG $.
      $( [2-Sep-2015] $)
  $}
 
  $( Now a series of auxiliary theorems. $)
  
  ${  
    eucr.1     $e |- p = q $.
    eucr.2     $e |- p = r $.
    $( A commuted - or reversed - version of ax-euc. $)
    eucr       $p |- q = r $=
      ( sym trans ) BACABDFEG $.
      $( [2-Sep-2015] $)
  $}

  ${  
    subr.1     $e |- p = q $.
    $( A commuted version of ax-sub $)
    subr       $p |- r p = r q $= 
      ( juxt ax-sub ax-cmm eucr ) BCEZCAEZCBEACEIJABCDFACGHBCGH $.
      $( [2-Sep-2015] $)
  $}

  ${  
    subst.1    $e |- p = q $.
    $( More versions of the substitution principle. Our lack of access to the
       implicit commutativity of 2D forces us to spell out each case. $)
    subst      $p |- u p v = u q v $= 
      ( juxt ax-sub subr ) ADFBDFCABDEGH $.
      $( [2-Sep-2015] $) 
    substr     $p |- u p v = v q u $=
      ( juxt ax-sub ax-cmm trans subr ) CAFDFCDFBFDBFZCFADFZKCLBDFKABDEGBDHIJCK
      HI $.
      $( [2-Sep-2015] $)
    subb1      $p |- w ( u p v ) x = w ( u q v ) x $=  
      ( juxt encl subst ax-beq ) CAHDHZICBHDHZIEFLMABCDGJKJ $.
      $( [2-Sep-2015] $)
    subb3      $p |- w ( u p v ) x = w ( v q u ) x  $= 
      ( juxt encl substr ax-beq subst ) CAHDHZIDBHCHZIEFMNABCDGJKL $.
      $( [2-Sep-2015] $)
  $}

  ${ 
    quad.1     $e |- p = q $.
    quad.2     $e |- r = s $.
    quad       $p |- p r = q s $=
      ( juxt void subst trans ) ACGBCGBDGABHCEICDBHFIJ $.
      $( [2-Sep-2015] $)
  $}

  ${
    ins.1      $e |- p q = r s $.
    ins        $p |- p v q = r v s $= 
      ( juxt ax-cmm ax-sub subr trans ) AEGZBGZECGZDGZCEGZDGMEAGZBGOLQBAEHIABGC
      DGEFJKNPDECHIK $.
      $( [3-Sep-2015] $)
  $}
 
  cmmbx      $p |- x ( u p v q w ) y = x ( u q v p w ) y $= 
    ( juxt id substr subb1 ) ADHBHBDHAHCEFGDDABDIJK $.
    $( [2-Sep-2015] $)

  ${ 
    quadbx.1   $e |- p = q $.
    quadbx.2   $e |- r = s $.
    quadbx     $p |- x ( u p v r w ) y = x ( u q v s w ) y  $= 
      ( juxt quad ins subb1 ) AFLCLBFLDLEGHIACBDFABCDJKMNO $.
      $( [3-Sep-2015] $)
  $}

  $( It's hard to know where to stop with auxiliary theorems. If we choose 
     to prove the two additional statements:
         $p |- x ( v p u ) w = w ( u r v ) x $.
         $p |- x ( v q u ) w = w ( u r v ) x $.
     we can reduce the proof of C9-cro by a hundred steps. $)

$( 
=============================================================================
                          Laws of Form (J1, J2) 
  
  The 'arithmetic' of LoF consists of two equations (LoF, p. 12):

  I1. Number   () () = ()
  I2. Order    (())  =   
  
  As mentioned, one of the models of LoF is the propositional calculus. 
  Briefly,
   
  T             <=>    ()
  F             <=>     
  NOT p         <=>    (p)
  p OR q        <=>    p q   
  p AND q       <=>    ((p) (q))   
  p IMPLIES q   <=>    (p) q
  p IFF q       <=>    ((p) (q)) (p q)
  etc.

  Spencer-Brown begins with the axioms:

  J1. Position                 ((p)p) = 
  J2. Transposition            ((pr)(qr)) = ((p)(q))r

  and deduces the following consequences (LoF, pp. 28-35):

  C1. Reflexion                ((a)) = a
  C2. Generation               (ab)b = (a)b
  C3. Integration              ()a = ()
  C4. Occultation              ((a)b)a = a
  C5. Iteration                aa = a
  C6. Extension                ((a)(b))((a)b) = a
  C7. Echelon                  (((a)b)c) = (ac)((b)c)
  C8. Modified transposition   ((a)(br)(cr)) = ((a)(b)(c))((a)(r))
  C9. Crosstransposition       (((b)(r))((a)(r))((x)r)((y)r)) = ((r)ab)(rxy)

  While this metamath version follows LoF, it does not attempt to mimic 
  Spencer-Brown's specific steps. For example, theorem C5 is derived before C4 
  (we retain LoF's original numbering of theorems to facilitate 
  cross-references).

============================================================================= 
$)

  J1-pos $a |- ( ( p ) p ) = $.
  J2-tra $a |- ( ( p r ) ( q r ) ) = ( ( p ) ( q ) ) r $.

  $( ---- reflexion ---- $)

  C1-ref $p |- ( ( p ) ) =  p $=

    ( encl juxt void J1-pos ax-sub sym J2-tra ax-euc cmmbx subb1 trans quadbx ) 
    ABZBZOACBZNACBZCBZAOAOCBZBZROONCBZSCBZTONOCBZSCBZUBOUAOCZUDUEOUADONEZFGNAOH
    IUCUADSDDNODDDDDJKLUADDSDDUFKLSPDQDDDDDAODDDDDJQDAEGMLROBOCBZACAONAHUGDAOEF
    LL 
    $.
    $( [6-Sep-2015] $)


  $( ---- generation ---- $)

  C2-gen $p |- ( p q ) q = ( p ) q $=

    ( encl juxt J2-tra void C1-ref quadbx trans J1-pos subb1 eucr ) ACZBDZCZBCZ
    BDCZDCZABDCBDZNRMCZPCZDCBDSMPBETAUABFFFFBAGBGHIROCNQFOFFFBJKNGIL $.
    $( [6-Sep-2015] $)


  $( ---- integration- ---- $)

  C3-int $p |- ( ) p  = ( ) $=

    ( encl juxt void C2-gen C1-ref J1-pos ax-beq eucr ) ABACZDBZACKDAEJBZBJKJFL
    DAGHII $.
    $( [6-Sep-2015] $)


  $( ---- iteration ---- $)

  C5-ite $p |- p p = p $=
  
    ( encl juxt C2-gen void C1-ref subst trans J1-pos eucr ) ABZACBZACZAACZAMKB
    ZACNKADOAEAAFGHLEEAAIGJ $.
    $( [6-Sep-2015] $)


  $( ---- occultation ---- $)

  C4-occ $p |- ( ( p ) q ) p = p $=

    ( encl juxt void J2-tra C1-ref subb1 trans C5-ite eucr C3-int subst ) ACZBD
    CADZECZCZADZAOPBCZCZDZCADZRONSADCZDCZUBAADZCZUCDCZOUDUGNTDCADOASAFTBNEEABGH
    IUFNEUCEEUEAEEEEAJHHKESAFIUAPEEEATLHIQEEAEGMI $.
    $( [6-Sep-2015] $)


  $( ---- extension ---- $)

  C6-ext $p |- ( ( p ) ( q ) ) ( ( p ) q ) = p  $=

    ( encl juxt C1-ref void cmmbx quadbx J2-tra trans ax-beq J1-pos subb1 eucr
    ) ACZBCZDCZOBDCZDZOCZASCZCZSTSEUBPCPDCZODZCTUAUDUAPODCZBODCZDCUDQUERUFFFFFF
    OPFFFFFGOBFFFFFGHPBOIJKUCFFOFFPLMJNAEJ $.
    $( [6-Sep-2015] $)


  $( ---- echelon ---- $)

  C7-ech $p |- ( ( ( p ) q ) r ) = ( p r ) ( ( q ) r ) $=

    ( juxt encl J2-tra ax-beq void C1-ref subb1 trans eucr ) ACDEBEZCDEDZEZEZAE
    ZBDECDZEZNPQMEZDECDZESOUAAMCFGUARTBQHHCBIJGKNIL $.
    $( [6-Sep-2015] $)


  $( ---- modified transposition ---- $)

  C8-mod $p |- ( ( p ) ( q s ) ( r s ) ) = 
               ( ( p ) ( q ) ( r ) ) ( ( p ) ( s ) ) $=

    ( encl juxt void C1-ref subb1 J2-tra ax-beq subb3 eucr C7-ech cmmbx quad 
    trans ) AEZBDFEZFCDFEZFEZBEZCEZFZEDFZEZRFEZRUBFUCFEZRDEZFEZFZRSTFZEZEZFEUAU
    GUNULRGGGULHIUNUFRGGGUMUEBCDJKLMUGUDRFEZUIRFEZFUKUDDRNUOUHUPUJUDRGGGGGOUIRG
    GGGGOPQQ $.
    $( [6-Sep-2015] $)


  $( ---- crosstransposition ---- $)

  C9-cro $p |- ( ( ( q ) ( p ) ) ( ( r ) ( p ) ) ( ( s ) p ) ( ( t ) p ) ) =
               ( ( p ) q r ) ( p s t )  $=

    ( encl juxt C1-ref J2-tra quadbx trans eucr subb3 C8-mod subb1 C2-gen cmmbx
    void ax-beq C6-ext ) BFZAFZGFZCFZUBGFZGZDFZAGFZGEFZAGFZGFDEGZFZAGZFZUCGUEGF
    ZUBBGCGFZADGEGFZGZUHUJGZUNUFRRRUSFZFUSUNUSHUTUMUTUGFZUIFZGFAGUMUGUIAIVADVBE
    RRRRADHEHJKSLMUOUNBGCGZFZUKAGFZGZURUOVDULFZAGZFGZVFUOVDUNAGZFGZVIUOVDUNUBFZ
    GFZGZVKUOUNUAFZGUDFZGFVMGVNUMUAUDUBNVOBVPCUNRRRVMBHCHJKVLAUNRVDRAHZOKVJVHRR
    VDRULAPOKVGUKRAVDRUKHOKVCVEGFVEGZVFURVCVEPVRAULGFZBGCGZUQGFVEGZURUNVSVEUQRB
    CGZRRVEULARRRRRQUKARRRRRQJVLULGFZBGCGZVLDGEGFZGFVEGZWAURWDVTWEUQRRRRVEVLARU
    LRWBVQOVLARUKRRVQOJWFWCWEGZBGCGFVEGZURWBWEWCRRRVEQWHUPVEGURWGUBRWBRVEUBUKTO
    UKARRRUPRQKKLKLKK $.
    $( [6-Sep-2015] $)





$( 
  lof.mm    version 0.1.0    Copyright (c) 2015 naipmoro
  This file is made available under the MIT License: 
  http://opensource.org/licenses/MIT

  lof.mm presents metamath derivations of the Primary Algebra from
  Spencer-Brown, G. (1969) Laws of Form (Allen & Unwin, London),
  hereafter cited as LoF.

  The 'arithmetic' of LoF consists of two equations:

  I1. Number   () () = ()
  I2. Order    (())  =   
  
  The algebra derived from this basis has a number of models, most
  significantly Boolean algebra and sentential logic. Briefly,
   
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

  While the first metamath version below follows this approach, it does not
  attempt to mimic Spencer-Brown's specific steps. For example, theorem C5
  is derived before C4.
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

  $( The next three statements will provide a recursive definition of 'form': 
       1. Empty space is a form.
       2. If p is a form, enclosing it in parentheses as (p) is a form. 
       3. If p and q are forms, juxtaposing them as p q is a form. 

     LoF is a 2-dimensional topological formalism in which a closed curve 
     (a boundary) is the only object of investigation, and in which the only 
     properties of interest are whether a given boundary is inside or outside 
     of another boundary, intersecting boundaries not being allowed. Variables 
     p q r ... will range over possible arrangements of boundaries (which are 
     the forms). Given the topological nature of the system, note that the
     'operations' are implicitly commutative. It is now common to call LoF
     a 'boundary algebra'.  

     Transferring this system to a linear notation involves compromises. As 
     has become standard, we use matching parentheses (...) to represent 
     boundaries. And we need to explicitly state the commutative property.
  $)
    
  void  $a form $.         $( Empty space is a form. $)
  encl  $a form ( p ) $.   $( If p is a form, then (p) is a form. $)
  juxt  $a form p q $.     $( If p and q are forms, then p q is a form. $)


  $( ---------- Axioms of equality ----------- 
   
     We never define the symbol '=' but it will turn out to obey the expected
     laws of an equivalence relation. Specifically, from the general axiom
     that two things equal to the same thing are equal to each other and from 
     the commutativity of LoF, we derive the reflexivity, symmetry, and 
     transitivity of '='. 
  $)
   
  $( Two things equal to the same thing are equal to each other. $)  
  ${  
    tran.1     $e |- p = q   $.
    tran.2     $e |- r = q   $.
    tran       $a |- p = r   $.  
  $}
   
  $( --------- LoF specific axioms of equality ---------- $)

  $( The principle of substitution can be considered a general axiom of 
     equality, but it's expressed differently in each formal system, depending 
     on that system's laws of combination. LoF's two laws of combination are 
     juxtaposition and enclosure by parentheses. The principle can also be 
     expressed constructively: applying the same operation to equal things 
     results in equal things. $)
  
  $( Appending the same form to two equal forms leaves two equal forms. $)
  ${  
    sub.1      $e |- p = q $.
    sub        $a |- p r = q r $.  
  $}
 
  $( Enclosing two equal forms leaves two equal forms. $)
  ${  
    beq.1      $e |- p = q $.
    beq        $a |- ( p ) = ( q ) $.  
  $}

  $( Commutativity of LoF $)
    comm       $a |- p q = q p $.
  
  
  $( ----------- Equality consequences ----------- $)

  $( '=' is reflexive. $)
    id         $p |- p = p  $=
      ( void comm ) ABC $.
      $( [6-Sep-2015] $)

  $( '=' is symmetric. $)
  ${  
    sym.1      $e |- p = q $.
    sym        $p |- q = p $=
      ( id tran ) BBABDCE $.
      $( [2-Sep-2015] $)
  $}

  $( '=' is transitive. $)
  ${  
    trans.1    $e |- p = q $.
    trans.2    $e |- q = r $.
    trans      $p |- p = r $=
      ( sym tran ) ABCDBCEFG $.
      $( [2-Sep-2015] $)
  $}
 
  $( A commuted - or reversed - version of tran. $)
  ${  
    tranr.1    $e |- p = q $.
    tranr.2    $e |- p = r $.
    tranr      $p |- q = r $=
      ( sym trans ) BACABDFEG $.
      $( [2-Sep-2015] $)
  $}

  $( A commuted version of sub $)
  ${  
    subr.1     $e |- p = q $.
    subr       $p |- r p = r q $= 
      ( juxt sub comm tranr ) BCEZCAEZCBEACEIJABCDFACGHBCGH $.
      $( [2-Sep-2015] $)
  $}

  $( More useful versions of the substitution principle $)
  ${  
    subst.1    $e |- p = q $.
    subst      $p |- u p v = u q v $= 
      ( juxt sub subr ) ADFBDFCABDEGH $.
      $( [2-Sep-2015] $) 
    substr     $p |- u p v = v q u $=
      ( juxt sub comm trans subr ) CAFDFCDFBFDBFZCFADFZKCLBDFKABDEGBDHIJCKHI $.
      $( [2-Sep-2015] $)
    subb1      $p |- w ( u p v ) x = w ( u q v ) x $=  
      ( juxt encl subst beq ) CAHDHZICBHDHZIEFLMABCDGJKJ $.
      $( [2-Sep-2015] $)
    subb3      $p |- w ( u p v ) x = w ( v q u ) x  $= 
      ( juxt encl substr beq subst ) CAHDHZIDBHCHZIEFMNABCDGJKL $.
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
      ( juxt comm sub subr trans ) AEGZBGZECGZDGZCEGZDGMEAGZBGOLQBAEHIABGCDGEFJ
      KNPDECHIK $.
      $( [3-Sep-2015] $)
  $}

  $( Further rules to ease subsequent derivations. $)
 
    commbx     $p |- x ( u p v q w ) y = x ( u q v p w ) y $= 
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
                          Laws of Form, Version 1 
============================================================================= 
$)

  J1-pos $a |- ( ( p ) p ) = $.
  J2-tra $a |- ( ( p r ) ( q r ) ) = ( ( p ) ( q ) ) r $.

  $( ----------- reflexion ------------- $)

  C1-ref $p |- ( ( p ) ) =  p $=

    ( encl juxt void J1-pos sub sym J2-tra tran commbx subb1 trans quadbx ) ABZ
    BZOACBZNACBZCBZAOAOCBZBZROONCBZSCBZTONOCBZSCBZUBOUAOCZUDUEOUADONEZFGNAOHIUC
    UADSDDNODDDDDJKLUADDSDDUFKLSPDQDDDDDAODDDDDJQDAEGMLROBOCBZACAONAHUGDAOEFLL 
    $.
    $( [6-Sep-2015] $)


  $( ----------- generation ------------ $)

  C2-gen $p |- ( p q ) q = ( p ) q $=

    ( encl juxt J2-tra void C1-ref quadbx trans J1-pos subb1 tranr ) ACZBDZCZBC
    ZBDCZDCZABDCBDZNRMCZPCZDCBDSMPBETAUABFFFFBAGBGHIROCNQFOFFFBJKNGIL $.
    $( [6-Sep-2015] $)


  $( ---------- integration- ---------- $)

  C3-int $p |- ( ) p  = ( ) $=

    ( encl juxt void C2-gen C1-ref J1-pos beq tranr ) ABACZDBZACKDAEJBZBJKJFLDA
    GHII $.
    $( [6-Sep-2015] $)


  $( ----------- iteration ------------ $)

  C5-ite $p |- p p = p $=
  
    ( encl juxt C2-gen void C1-ref subst trans J1-pos tranr ) ABZACBZACZAACZAMK
    BZACNKADOAEAAFGHLEEAAIGJ $.
    $( [6-Sep-2015] $)


  $( ----------- occultation ------------ $)

  C4-occ $p |- ( ( p ) q ) p = p $=

    ( encl juxt void J2-tra C1-ref subb1 trans C5-ite tranr C3-int subst ) ACZB
    DCADZECZCZADZAOPBCZCZDZCADZRONSADCZDCZUBAADZCZUCDCZOUDUGNTDCADOASAFTBNEEABG
    HIUFNEUCEEUEAEEEEAJHHKESAFIUAPEEEATLHIQEEAEGMI $.
    $( [6-Sep-2015] $)


  $( ----------- extension ------------ $)

  C6-ext $p |- ( ( p ) ( q ) ) ( ( p ) q ) = p  $=

    ( encl juxt C1-ref void commbx quadbx J2-tra trans beq J1-pos subb1 tranr ) 
    ACZBCZDCZOBDCZDZOCZASCZCZSTSEUBPCPDCZODZCTUAUDUAPODCZBODCZDCUDQUERUFFFFFFOP
    FFFFFGOBFFFFFGHPBOIJKUCFFOFFPLMJNAEJ $.
    $( [6-Sep-2015] $)


  $( ---------- echelon ----------- $)

  C7-ech $p |- ( ( ( p ) q ) r ) = ( p r ) ( ( q ) r ) $=

    ( juxt encl J2-tra beq void C1-ref subb1 trans tranr ) ACDEBEZCDEDZEZEZAEZB
    DECDZEZNPQMEZDECDZESOUAAMCFGUARTBQHHCBIJGKNIL $.
    $( [6-Sep-2015] $)


  $( ---------- modified transposition ----------- $)

  C8-mod $p |- ( ( p ) ( q s ) ( r s ) ) = 
               ( ( p ) ( q ) ( r ) ) ( ( p ) ( s ) ) $=

    ( encl juxt void C1-ref subb1 J2-tra beq subb3 tranr C7-ech commbx quad 
    trans ) AEZBDFEZFCDFEZFEZBEZCEZFZEDFZEZRFEZRUBFUCFEZRDEZFEZFZRSTFZEZEZFEUAU
    GUNULRGGGULHIUNUFRGGGUMUEBCDJKLMUGUDRFEZUIRFEZFUKUDDRNUOUHUPUJUDRGGGGGOUIRG
    GGGGOPQQ $.
    $( [6-Sep-2015] $)


  $( ------------ crosstransposition ----------- $)

  C9-cro $p |- ( ( ( q ) ( p ) ) ( ( r ) ( p ) ) ( ( s ) p ) ( ( t ) p ) ) =
               ( ( p ) q r ) ( p s t )  $=

    ( encl juxt C1-ref J2-tra quadbx trans tranr subb3 C8-mod subb1 C2-gen 
    commbx void beq C6-ext ) BFZAFZGFZCFZUBGFZGZDFZAGFZGEFZAGFZGFDEGZFZAGZFZUCG
    UEGFZUBBGCGFZADGEGFZGZUHUJGZUNUFRRRUSFZFUSUNUSHUTUMUTUGFZUIFZGFAGUMUGUIAIVA
    DVBERRRRADHEHJKSLMUOUNBGCGZFZUKAGFZGZURUOVDULFZAGZFGZVFUOVDUNAGZFGZVIUOVDUN
    UBFZGFZGZVKUOUNUAFZGUDFZGFVMGVNUMUAUDUBNVOBVPCUNRRRVMBHCHJKVLAUNRVDRAHZOKVJ
    VHRRVDRULAPOKVGUKRAVDRUKHOKVCVEGFVEGZVFURVCVEPVRAULGFZBGCGZUQGFVEGZURUNVSVE
    UQRBCGZRRVEULARRRRRQUKARRRRRQJVLULGFZBGCGZVLDGEGFZGFVEGZWAURWDVTWEUQRRRRVEV
    LARULRWBVQOVLARUKRRVQOJWFWCWEGZBGCGFVEGZURWBWEWCRRRVEQWHUPVEGURWGUBRWBRVEUB
    UKTOUKARRRUPRQKKLKLKK $.
    $( [6-Sep-2015] $)





$( lof.mm  version 0.1.0 
   lof.mm presents metamath derivations of the Primary Algebra from
   Spencer-Brown, G. (1969) Laws of Form (Allen & Unwin, London),
   hereafter cited as LoF.

   The 'arithmetic' of LoF is based on two equations:

   I1. Number   () () = ()
   I2. Order    (())  =   
  
   The algebra derived from these equations has at least two significant 
   models: Boolean algebra and sentential logic. Briefly,
   
   T            <=>    ()
   F            <=>     
   NOT p        <=>    (p)
   p OR q       <=>    p q   
   p AND q      <=>    ((p) (q))   
   p IMPLIES q  <=>    (p) q
   etc.

   Spencer-Brown begins with the following axioms:

   J1. Position                 ((p)p) = 
   J2. Transposition            ((pr)(qr)) = ((p)(q))r

   and deduces the series of consequences (LoF, pp. 28-35):

   C1. Reflexion                ((a)) = a
   C2. Generation               (ab)b = (a)b
   C3. Integration              ()a = ()
   C4. Occultation              ((a)b)a = a
   C5. Iteration                aa = a
   C6. Extension                ((a)(b))((a)b) = a
   C7. Echelon                  (((a)b)c) = (ac)((b)c)
   C8. Modified transposition   ((a)(br)(cr)) = ((a)(b)(c))((a)(r))
   C9. Crosstransposition       (((b)(r))((a)(r))((x)r)((y)r)) = ((r)ab)(rxy)

   Later consequences depend on earlier ones. Although the metamath version 1
   follows this general approach, it doesn't attempt to mimic Spencer-Brown's 
   specific steps.
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

$( ---------- The 3 types of form ---------- $)

  $( Empty space is a form. $)
    void  $a form $.

  $( A form bounded by parentheses, aka a crossed form, is a form. $)
    crss  $a form ( p ) $.

  $( The juxtaposition of two forms is a form. $)
    juxt  $a form p q $.

  $( We consider a wff to be p = q, but don't actually need to specify it. 
     The following 4 axioms .................. $)

$( ---------- general axioms of equality ----------- $)
   
  
 
  $( Two things equal to the same thing are equal to each other. $)  
  ${  
    tran.1     $e |- p = q   $.
    tran.2     $e |- r = q   $.
    tran       $a |- p = r   $.  
  $}
   
  $( --------- LoF specific axioms of equality ----------- $)

  $( The principle of substitution is a general axiom of equality, but it's
     expressed differently in each formal system, depending on that system's 
     laws of combination. LoF's two laws of combination are concatenation and
     and enclosure by parentheses. The principle can also be expressed 
     constructively: applying the same operation to equal things results 
     in equal things. $)
  
  ${  
    sub.1      $e |- p = q $.
    sub        $a |- p r = q r $.  
  $}
 
  $( Boundary equality - equal forms that are crossed remain equal. $)
  ${  
    beq.1      $e |- p = q $.
    beq        $a |- ( p ) = ( q ) $.  
  $}

  $( Commutativity of LoF $)
    comm       $a |- p q = q p $.
  
  
$( ----------- Equality consequences ----------- $)

  $( Equality is reflexive. $)
    id         $p |- p = p  $=
      ( void comm ) ABC $.
      $( [6-Sep-2015] $)

  $( Equality is symmetric. $)
  ${  
    sym.1      $e |- p = q $.
    sym        $p |- q = p $=
      ( id tran ) BBABDCE $.
      $( [2-Sep-2015] $)
  $}

  $( Equality is transitive. $)
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
      ( juxt crss subst beq ) CAHDHZICBHDHZIEFLMABCDGJKJ $.
      $( [2-Sep-2015] $)
    subb3      $p |- w ( u p v ) x = w ( v q u ) x  $= 
      ( juxt crss substr beq subst ) CAHDHZIDBHCHZIEFMNABCDGJKL $.
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

  $( It's hard to know where to stop with auxiliary theorems. For example,
     if we bother to prove the two statements
         $p |- x ( v p u ) w = w ( u r v ) x $.
         $p |- x ( v q u ) w = w ( u r v ) x $.
     we can reduce the proof of C9-cro by a hundred steps. $)

$( -------------- Laws of Form ---------------- $)

J1-pos $a |- ( ( p ) p ) = $.
J2-tra $a |- ( ( p r ) ( q r ) ) = ( ( p ) ( q ) ) r $.

$( ----------- reflexion ------------- $)

C1-ref $p |- ( ( p ) ) =  p $=

  ( crss juxt void J1-pos sub sym J2-tra tran commbx subb1 trans quadbx ) ABZBZ
  OACBZNACBZCBZAOAOCBZBZROONCBZSCBZTONOCBZSCBZUBOUAOCZUDUEOUADONEZFGNAOHIUCUADS
  DDNODDDDDJKLUADDSDDUFKLSPDQDDDDDAODDDDDJQDAEGMLROBOCBZACAONAHUGDAOEFLL $.
  $( [6-Sep-2015] $)


$( ----------- generation ------------ $)

C2-gen $p |- ( p q ) q = ( p ) q $=

  ( crss juxt J2-tra void C1-ref quadbx trans J1-pos subb1 tranr ) ACZBDZCZBCZB
  DCZDCZABDCBDZNRMCZPCZDCBDSMPBETAUABFFFFBAGBGHIROCNQFOFFFBJKNGIL $.
  $( [6-Sep-2015] $)


$( ---------- integration- ---------- $)

C3-int $p |- ( ) p  = ( ) $=

  ( crss juxt void C2-gen C1-ref J1-pos beq tranr ) ABACZDBZACKDAEJBZBJKJFLDAGH
  II $.
  $( [6-Sep-2015] $)


$( ----------- iteration ------------ $)

C5-ite $p |- p p = p $=
  
( crss juxt C2-gen void C1-ref subst trans J1-pos tranr ) ABZACBZACZAACZAMKBZ
  ACNKADOAEAAFGHLEEAAIGJ $.
  $( [6-Sep-2015] $)


$( ----------- occultation ------------ $)

C4-occ $p |- ( ( p ) q ) p = p $=

  ( crss juxt void J2-tra C1-ref subb1 trans C5-ite tranr C3-int subst ) ACZBDC
  ADZECZCZADZAOPBCZCZDZCADZRONSADCZDCZUBAADZCZUCDCZOUDUGNTDCADOASAFTBNEEABGHIUF
  NEUCEEUEAEEEEAJHHKESAFIUAPEEEATLHIQEEAEGMI $.
  $( [6-Sep-2015] $)


$( ----------- extension ------------ $)

C6-ext $p |- ( ( p ) ( q ) ) ( ( p ) q ) = p  $=

  ( crss juxt C1-ref void commbx quadbx J2-tra trans beq J1-pos subb1 tranr ) A
  CZBCZDCZOBDCZDZOCZASCZCZSTSEUBPCPDCZODZCTUAUDUAPODCZBODCZDCUDQUERUFFFFFFOPFFF
  FFGOBFFFFFGHPBOIJKUCFFOFFPLMJNAEJ $.
  $( [6-Sep-2015] $)


$( ---------- echelon ----------- $)

C7-ech $p |- ( ( ( p ) q ) r ) = ( p r ) ( ( q ) r ) $=

  ( juxt crss J2-tra beq void C1-ref subb1 trans tranr ) ACDEBEZCDEDZEZEZAEZBDE
  CDZEZNPQMEZDECDZESOUAAMCFGUARTBQHHCBIJGKNIL $.
  $( [6-Sep-2015] $)


$( ---------- modified transposition ----------- $)

C8-mod $p |- ( ( p ) ( q s ) ( r s ) ) = 
             ( ( p ) ( q ) ( r ) ) ( ( p ) ( s ) ) $=

  ( crss juxt void C1-ref subb1 J2-tra beq subb3 tranr C7-ech commbx quad trans
  ) AEZBDFEZFCDFEZFEZBEZCEZFZEDFZEZRFEZRUBFUCFEZRDEZFEZFZRSTFZEZEZFEUAUGUNULRGG
  GULHIUNUFRGGGUMUEBCDJKLMUGUDRFEZUIRFEZFUKUDDRNUOUHUPUJUDRGGGGGOUIRGGGGGOPQQ
  $.
  $( [6-Sep-2015] $)


$( ------------ crosstransposition ----------- $)

C9-cro $p |- ( ( ( q ) ( p ) ) ( ( r ) ( p ) ) ( ( s ) p ) ( ( t ) p ) ) =
             ( ( p ) q r ) ( p s t )  $=

  ( crss juxt C1-ref J2-tra quadbx trans tranr subb3 C8-mod subb1 C2-gen commbx
  void beq C6-ext ) BFZAFZGFZCFZUBGFZGZDFZAGFZGEFZAGFZGFDEGZFZAGZFZUCGUEGFZUBBG
  CGFZADGEGFZGZUHUJGZUNUFRRRUSFZFUSUNUSHUTUMUTUGFZUIFZGFAGUMUGUIAIVADVBERRRRADH
  EHJKSLMUOUNBGCGZFZUKAGFZGZURUOVDULFZAGZFGZVFUOVDUNAGZFGZVIUOVDUNUBFZGFZGZVKUO
  UNUAFZGUDFZGFVMGVNUMUAUDUBNVOBVPCUNRRRVMBHCHJKVLAUNRVDRAHZOKVJVHRRVDRULAPOKVG
  UKRAVDRUKHOKVCVEGFVEGZVFURVCVEPVRAULGFZBGCGZUQGFVEGZURUNVSVEUQRBCGZRRVEULARRR
  RRQUKARRRRRQJVLULGFZBGCGZVLDGEGFZGFVEGZWAURWDVTWEUQRRRRVEVLARULRWBVQOVLARUKRR
  VQOJWFWCWEGZBGCGFVEGZURWBWEWCRRRVEQWHUPVEGURWGUBRWBRVEUBUKTOUKARRRUPRQKKLKLKK
  $.
  $( [6-Sep-2015] $)





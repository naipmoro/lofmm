$(
  lofset.mm
  version 0.1.1
  Copyright (C) 2017 naipmoro

  This file is made available under the MIT License:
  http://opensource.org/licenses/MIT

  This file contains verbatim excerpts from set.mm
  (found at https://github.com/metamath/set.mm/blob/master/set.mm) which
  is released under the CC0 1.0 Universal public domain license.
$)

$(
  -----------------------------------------------------------------------------
                              0. Introduction
  -----------------------------------------------------------------------------

  In [Naip] I presented metamath derivations of Spencer-Brown's Primary Algebra
  (details of the algebra, hereafter cited as "LoF", can be found in chapter 6
  of [Spencer-Brown]).  [Naip] was a  stand-alone project that, for maximum
  readability, intentionally bypassed compatibility with set.mm, metamath's
  ongoing formalization of mathematics.  Here I present a version which is more
  than just compatible; I derive set.mm's propositional calculus from LoF. 
  There is nothing surprising in this -- classical propositional logic is one
  of the interpretations of LoF (Boolean algebra is another).  The real
  interest lies in the means of derivation.

  First a note about notation.  To avoid conflict with set.mm, I use grave
  accented brackets, "[`" and "`]" to represent the boundary (or "cross") of
  LoF.  This seemed to me to entail the least visual noise (readers may
  disagree).  Similarly I use ".=" for the equals sign.

  LoF is an example of an equational logic (although I show that, technically,
  equations can be avoided).  In other words, axioms and theorems are stated in
  the form P .= Q.  Transitioning from this to the implicational form
  characteristic of classical propositional logic is an interesting problem.  I
  believe the technique chosen here is among the simplest, relying on a single
  additional axiom ~ lofax-ded , the equational analogue of modus ponens:

  ${
    lofax-ded.1 $e |- ph $.
    lofax-ded.2 $e |- ph .= ps $.
    lofax-ded   $a |- ps $.
  $}

  With this tool in hand, and with appropriate definitions of "implies" and
  "not", I prove the axioms of metamath, ~ ax-1 , ~ ax-2 , ~ ax-3 , and
  ~ ax-mp , as theorems of LoF.
$)

$(
  -----------------------------------------------------------------------------
                            1. The alphabet of LoF
  -----------------------------------------------------------------------------
$)

  $( Declare the primitive constant symbols for the Primary Algebra. $)
  $c [` $. $( Left bracket $)
  $c `] $. $( Right bracket $)
  $c wff $. $( Well-formed formula symbol (read:  "the following symbol
               sequence is a wff") $)
  $c |- $. $( Turnstile (read:  "the following symbol sequence is provable" or
              'a proof exists for") $)

  $( wff variable sequence:  ph ps ch th ta et ze si rh mu la ka $)
  $( Introduce some variable names we will use to represent well-formed
     formulas (wff's). $)
  $v ph $.  $( Greek phi $)
  $v ps $.  $( Greek psi $)
  $v ch $.  $( Greek chi $)
  $v th $.  $( Greek theta $)
  $v ta $.  $( Greek tau $)
  $v et $.  $( Greek eta $)
  $v ze $.  $( Greek zeta $)
  $v si $.  $( Greek sigma $)
  $v rh $.  $( Greek rho $)
  $v mu $.  $( Greek mu $)
  $v la $.  $( Greek lambda $)
  $v ka $.  $( Greek kappa $)

  $( Specify some variables that we will use to represent wff's.
     The fact that a variable represents a wff is relevant only to a theorem
     referring to that variable, so we may use $f hypotheses.  The symbol
     ` wff ` specifies that the variable that follows it represents a wff. $)
  $( Let variable ` ph ` be a wff. $)
  wph $f wff ph $.
  $( Let variable ` ps ` be a wff. $)
  wps $f wff ps $.
  $( Let variable ` ch ` be a wff. $)
  wch $f wff ch $.
  $( Let variable ` th ` be a wff. $)
  wth $f wff th $.
  $( Let variable ` ta ` be a wff. $)
  wta $f wff ta $.
  $( Let variable ` et ` be a wff. $)
  wet $f wff et $.
  $( Let variable ` ze ` be a wff. $)
  wze $f wff ze $.
  $( Let variable ` si ` be a wff. $)
  wsi $f wff si $.
  $( Let variable ` rh ` be a wff. $)
  wrh $f wff rh $.
  $( Let variable ` mu ` be a wff. $)
  wmu $f wff mu $.
  $( Let variable ` la ` be a wff. $)
  wla $f wff la $.
  $( Let variable ` ka ` be a wff. $)
  wka $f wff ka $.

$(
  -----------------------------------------------------------------------------
                       2. Recursive definition of LoF wffs
  -----------------------------------------------------------------------------
$)

  $( Empty space is a wff.  We will sometimes refer to it as the "unmarked
     state" and in our intended interpretation it will be identified with the
     value False. $)
  lofdf-void $a wff $.

  $( If ` ph ` is a wff, so is ` [ ` ph ` ] ` . We say that " ` ph ` is 
     enclosed (or crossed, or marked)".  Combined with the previous definition,
     we see that ` [` `] ` , ` [` [` `] `] ` ,  ` [` ... [` [` `] `] ... `] `
     are all wffs.  We will call ` [` `] ` the "marked state" and identify it
     with the value True. $)
  lofdf-encl $a wff [` ph `] $.

  $( If ` ph ` and ` ps ` are wffs, so is ` ph ps ` .  This rule introduces
     technical ambiguity into the formal language and some of the more popular
     metamath parsers are unable to accomodate it.  However, since the system
     is inherently associative, this has no effect on the validity of the
     formal derivations and all proper validators will accept the results. $)
  lofdf-juxt $a wff ph ps $.

$(
  -----------------------------------------------------------------------------
                  3. The four primitive axioms of formal derivation
  -----------------------------------------------------------------------------

  In [Naip] equality, represented by "=", was one of the primitive constants of
  the language.  But the symbol is superfluous, as in a Boolean system equality
  and equivalence are synonyms.  Let us interpret the form
  ` [` [` ph `] [` ps `] `] [` ph ps `] ` to mean " ` ph ` equals (or is
  equivalent to) ` ps ` ".  All of LoF can be expressed accordingly, and I will
  call this the "unitary form" of LoF.  For demonstration purposes, I state the
  four primitive rules of LoF derivation and a handful of associated theorems
  in this form.  But what is theoretically possible is not always cognitively
  palatable, and I subsequently jettison this approach and return to explicit
  equations, what I call LoF's "normal form".
$)

  ${
    lofax-euc.1 $e |- [` [` ph `] [` ps `] `] [` ph ps `] $.
    lofax-euc.2 $e |- [` [` ch `] [` ps `] `] [` ch ps `] $.
    $( Read this as:  "If ` ph ` is equal to ` ps ` and ` ch ` is equal to
       ` ps ` , then we can assert that ` ph ` is equal to ` ch ` ".  In other
       words, two things equal to the same thing are equal to each other.
       This is Euclid's first Common Notion and, in an equational logic, this
       and its sibling, transitivity, are the main engine of derivation. $)
    lofax-euc $a |- [` [` ph `] [` ch `] `] [` ph ch `] $.
  $}

  $( We can rephrase Euclid's second and third Common Notions as: doing the
     same thing (e.g., applying the same operation) to equal things leaves
     equal things.  In light of LoF's two operations, enclosure and
     juxtaposition, this leads to the next two axioms (looked at differently,
     these can also be seen as substitution/replacement rules). $)

  ${
    lofax-beq.1 $e |- [` [` ph `] [` ps `] `] [` ph ps `] $.
    $( Read this as:  "If ` ph ` is equal to ` ps ` , then we can assert that
       ` [ ` ph ` ] ` is equal to ` [ ` ps ` ] ` ".  Enclosing equal forms
       leaves equal forms. $)
    lofax-beq $a |- [` [` [` ph `] `] [` [` ps `] `] `] [` [` ph `] [` ps `] `]
    $.
  $}

  ${
    lofax-sub.1 $e |- [` [` ph `] [` ps `] `] [` ph ps `] $.
    $( Read this as:  "If ` ph ` is equal to ` ps ` , then we can assert that
       ` ph ze ` is equal to ` ps ze ` ".  Juxtaposing the same form with equal
       forms leaves equal forms. $)
    lofax-sub $a |- [` [` ph ze `] [` ps ze `] `] [` ph ze ps ze `] $.
  $}

  $( Commutativity of LoF.  $)

  $( Read this as:  " ` ph ps ` is equal to ` ps ph ` ".  Of the four axioms,
     only this one is domain-specific. $)
  lofax-cmm $a |- [` [` ph ps `] [` ps ph `] `] [` ph ps ps ph `] $.

$(
  -----------------------------------------------------------------------------
                        4. Theorems of derivation
  -----------------------------------------------------------------------------

  If our target interpetation is to be satisfied, we should expect "equality"
  to meet the requirements of an equivalence relation: reflexivity, symmetry,
  and transitivity.  The next three theorems show that it does.
$)

  $( "Equality" is reflexive.  Read this theorem as:  " ` ph ` is equal to
      ` ph ` ".   (Contributed by naipmoro, 26-Jan-2017.) $)
  lofidu $p |- [` [` ph `] [` ph `] `] [` ph ph `] $=
    ( lofdf-void lofax-cmm ) ABC $.
    $( [26-Jan-2017] $)

  ${
    lofsymu.1 $e |- [` [` ph `] [` ps `] `] [` ph ps `] $.
    $( "Equality" is symmetric.  Read this theorem as:  "If ` ph ` is equal to
       ` ps ` , then we can assert that ` ps ` is equal to ` ph ` ".
       (Contributed by naipmoro, 26-Jan-2017.) $)
    lofsymu $p |- [` [` ps `] [` ph `] `] [` ps ph `] $=
      ( lofidu lofax-euc ) BBABDCE $.
      $( [26-Jan-2017] $)
  $}

  ${
    loftransu.1 $e |- [` [` ph `] [` ps `] `] [` ph ps `] $.
    loftransu.2 $e |- [` [` ps `] [` ch `] `] [` ps ch `] $.
    $( "Equality" is transitive.  Read this theorem as:  "If ` ph ` is equal to
       ` ps ` and ` ps ` is equal to ` ch ` , then we can assert that ` ph ` is
       equal to ` ch ` ".  (Contributed by naipmoro, 26-Jan-2017.) $)
    loftransu $p |- [` [` ph `] [` ch `] `] [` ph ch `] $=
      ( lofsymu lofax-euc ) ABCDBCEFG $.
      $( [26-Jan-2017] $)
  $}

$(
  -----------------------------------------------------------------------------
                     5. Introducing the notion of equality
  -----------------------------------------------------------------------------

  We can go only so far with the unitary form before reasoning becomes
  intolerably cumbersome.  Note that ".=" is a relation between wffs and not
  itself part of a wff, despite being defined in terms of a wff.
$)

  $c .= $. $( Equality (read:  "is equal to" or "is equivalent to") $)

  ${
    lofdf-equ.1 $e |- ph .= ps $.
    $( Define equality in terms of LoF's unitary formalism. $)
    lofdf-equ $a |- [` [` ph `] [` ps `] `] [` ph ps `] $.
  $}

  ${
    lofdf-uni.1 $e |- [` [` ph `] [` ps `] `] [` ph ps `] $.
    $( Translate LoF's unitary form into normal form. $)
    lofdf-uni $a |- ph .= ps $.
  $}

$(
  -----------------------------------------------------------------------------
                 6. Equality-based theorems of formal derivation
  -----------------------------------------------------------------------------

  The following theorems are LoF-specific versions of general transformation
  rules that apply to all commutative and associative structures.
$)

  ${
    lofeuc.1 $e |- ph .= ps $.
    lofeuc.2 $e |- ch .= ps $.
    $( The normal-form version of ~ lofax-euc .  (Contributed by naipmoro,
       26-Jan-2017.) $)
    lofeuc $p |- ph .= ch $=
      ( lofdf-equ lofax-euc lofdf-uni ) ACABCABDFCBEFGH $.
      $( [26-Jan-2017] $)
  $}

  ${
    lofbeq.1 $e  |- ph .= ps $.
    $( The normal-form version of ~ lofax-beq .  (Contributed by naipmoro,
       26-Jan-2017.) $)
    lofbeq $p |- [` ph `] .= [` ps `] $=
      ( lofdf-encl lofdf-equ lofax-beq lofdf-uni ) ADBDABABCEFG $.
      $( [26-Jan-2017] $)
  $}

  ${
    lofsub.1 $e |- ph .= ps $.
    $( The normal-form version of ~ lofax-sub .  (Contributed by naipmoro,
       26-Jan-2017.) $)
    lofsub $p |- ph ze .= ps ze $=
      ( lofdf-juxt lofdf-equ lofax-sub lofdf-uni ) ACEBCEABCABDFGH $.
      $( [26-Jan-2017] $)
  $}

  $( The normal-form version of ~ lofax-cmm .  (Contributed by naipmoro,
     26-Jan-2017.) $)
  lofcmm $p |- ph ps .= ps ph $=
    ( lofdf-juxt lofax-cmm lofdf-uni ) ABCBACABDE $.
    $( [26-Jan-2017] $)

  $( The normal-form version of ~ lofidu .  (Contributed by naipmoro,
     6-Sep-2015.) $)
  lofid $p |- ph .= ph $=
    ( lofdf-void lofcmm ) ABC $.
    $( [6-Sep-2015] $)

  ${
    lofsym.1 $e |- ph .= ps $.
    $( The normal-form version of ~ lofsymu .  (Contributed by naipmoro,
       2-Sep-2015.) $)
    lofsym $p |- ps .= ph $=
      ( lofid lofeuc ) BBABDCE $.
      $( [2-Sep-2015] $)
  $}

  ${
    loftrans.1 $e |- ph .= ps $.
    loftrans.2 $e |- ps .= ch $.
    $( The normal-form version of ~ loftransu .  (Contributed by naipmoro,
       2-Sep-2015.) $)
    loftrans $p |- ph .= ch $=
      ( lofsym lofeuc ) ABCDBCEFG $.
      $( [2-Sep-2015] $)
  $}

  ${
    lofeucr.1 $e |- ph .= ps $.
    lofeucr.2 $e |- ph .= ch $.
    $( A commuted - or reversed - version of ~ lofeuc .  (Contributed by
       naipmoro, 2-Sep-2015.) $)
    lofeucr $p |- ps .= ch $=
      ( lofsym loftrans ) BACABDFEG $.
      $( [2-Sep-2015] $)
  $}

  ${
    lofsubr.1 $e |- ph .= ps $.
    $( A commuted version of ~ lofsub .  (Contributed by naipmoro, 
       2-Sep-2015.) $)
    lofsubr $p |- et ph .= et ps $=
      ( lofdf-juxt lofsub lofcmm lofeucr ) BCEZCAEZCBEACEIJABCDFACGHBCGH $.
      $( [2-Sep-2015] $)
  $}

  $( More versions of replacement/substitution. $)
  ${
    lofsubst.1 $e |- ph .= ps $.
    $( Replace a form with an equal form within an extended form.  (Contributed
       by naipmoro, 2-Sep-2015.) $)
    lofsubst $p |- et ph ze .= et ps ze $=
      ( lofdf-juxt lofsub lofsubr ) ADFBDFCABDEGH $.     
      $( [2-Sep-2015] $)
    
    $( Replace a form with an equal form within a commuted extended form.
       (Contributed by naipmoro, 2-Sep-2015.) $)
    lofsubstr $p |- et ph ze .= ze ps et $=
      ( lofdf-juxt lofsub lofcmm loftrans lofsubr ) CAFDFCDFBFDBFZCFADFZKCLBDFK
      ABDEGBDHIJCKHI $.
      $( [2-Sep-2015] $)
      
    $( Replace a form with an equal form within a bounded extended form.
       (Contributed by naipmoro, 2-Sep-2015.) $)    
    lofsubb1 $p |- si [` et ph ze `] rh .= si [` et ps ze `] rh $=
      ( lofdf-juxt lofdf-encl lofsubst lofbeq ) CAHDHZICBHDHZIEFLMABCDGJKJ $.
      $( [2-Sep-2015] $)

    $( Replace a form with an equal form within a double-bounded extended form.
       (Contributed by naipmoro, 25-Feb-2017.) $)    
    lofsubbd1 $p |-  mu [` si [` et ph ze `] rh `] la 
                    .= mu [` si [` et ps ze `] rh `] la $=
      ( lofdf-juxt lofdf-encl lofdf-void lofsubb1 ) ECAJDJKJFJECBJDJKJFJLLGHABC
      DEFIMM $.
      $( [25-Feb-2017] $)

    $( Replace a form with an equal form within a bounded and commuted extended
       form.  (Contributed by naipmoro, 2-Sep-2015.) $)    
    lofsubb2 $p |- si [` et ph ze `] rh .= si [` ze ps et `] rh $=
      ( lofdf-juxt lofdf-encl lofsubstr lofbeq lofsubst ) CAHDHZIDBHCHZIEFMNABC
      DGJKL $.
      $( [2-Sep-2015] $)
  $}

  ${
    lofrep.1 $e |- ph .= ps $.
    lofrep.2 $e |- et ph ze .= mu $.
    $( Direct substitution into LHS of an equation.  (Contributed by naipmoro,
       18-Sep-2015.) $)
    lofrep $p |- et ps ze .= mu $=
      ( lofdf-juxt lofsubst lofeucr ) CAHDHCBHDHEABCDFIGJ $.
      $( [18-Sep-2015] $)
  $}

  ${
    lofreps.1 $e |- ph .= ps $.
    lofreps.2 $e |- mu .= et ph ze $.
    $( Direct substitution into RHS of an equation.  (Contributed by naipmoro,
      14-Feb-2017.) $)
    lofreps $p |- mu .= et ps ze $=
      ( lofdf-juxt lofsym lofrep ) CBHDHEABCDEFECAHDHGIJI $.
      $( [14-Feb-2017] $)
  $}

  ${
    lofrepbx.1 $e |- ph .= ps $.
    lofrepbx.2 $e |- si [` et ph ze `] rh .= mu $.
    $( Direct substitution into LHS of a bounded-form equation.  (Contributed
       by naipmoro, 18-Sep-2015.) $)
    lofrepbx $p |- si [` et ps ze `] rh .= mu $=
      ( lofdf-juxt lofdf-encl lofsubb1 lofeucr ) ECAJDJKJFJECBJDJKJFJGABCDEFHLI
      M $.
      $( [18-Sep-2015] $)
  $}

  ${
    lofrepbxs.1 $e |- ph .= ps $.
    lofrepbxs.2 $e |- mu .= si [` et ph ze `] rh $.
    $( Direct substitution into RHS of a bounded equation.  (Contributed
       by naipmoro, 14-Feb-2017.) $)
    lofrepbxs $p |- mu .= si [` et ps ze `] rh $=
      ( lofdf-juxt lofdf-encl lofsym lofrepbx ) ECBJDJKJFJGABCDEFGHGECAJDJKJFJI
      LML $.
      $( [14-Feb-2017] $)
  $}

  ${
    lofrepbd.1 $e |- ph .= ps $.
    lofrepbd.2 $e |- [` [` et ph ze `] `] .= mu $.
    $( Direct substitution into LHS of a double-bounded equation.
       (Contributed by naipmoro, 3-Oct-2015.) $)
    lofrepbd $p |- [` [` et ps ze `] `] .= mu $=
      ( lofdf-juxt lofdf-encl lofdf-void lofsubb1 lofbeq lofeucr ) CAHDHIZICBHD
      HIZIENOABCDJJFKLGM $.
      $( [3-Oct-2015] $)
  $}

  ${
    lofquad.1 $e |- ph .= ps $.
    lofquad.2 $e |- ch .= th $.
    $( Double substitution of equivalent forms.  (Contributed by naipmoro,
       2-Sep-2015.) $)
    lofquad $p |- ph ch .= ps th $=
      ( lofdf-juxt lofdf-void lofsubst loftrans ) ACGBCGBDGABHCEICDBHFIJ $.
      $( [2-Sep-2015] $)
  $}

  ${
    lofins.1 $e |- ph ps .= ch th $.
    $( Insert the same form into two equivalent forms.  (Contributed by
       naipmoro, 3-Sep-2015.) $)
    lofins $p |- ph ze ps .= ch ze th $=
      ( lofdf-juxt lofcmm lofsub lofsubr loftrans ) AEGZBGZECGZDGZCEGZDGMEAGZBG
      OLQBAEHIABGCDGEFJKNPDECHIK $.
      $( [3-Sep-2015] $)
  $}

  $( Extended commutativity.  (Contributed by naipmoro, 3-Sep-2015.) $)
  lofcmmx $p  |- et ph ze ps si .= et ps ze ph si $=
    ( lofdf-juxt lofcmm lofins lofsubst ) ADFBFBDFAFCEABBADABGHI $.
    $( [3-Sep-2015] $)

  $( Bounded and extended commutativity.  (Contributed by naipmoro,
     2-Sep-2015.) $)
  lofcmmbx $p |- rh [` et ph ze ps si `] mu .= rh [` et ps ze ph si `] mu $=
    ( lofdf-juxt lofid lofsubstr lofsubb1 ) ADHBHBDHAHCEFGDDABDIJK $.
    $( [2-Sep-2015] $)

  $( Double-bounded and extended commutativity.  (Contributed by naipmoro,
     25-Feb-2017.) $)
  lofcmmbdx $p |- la [` rh [` et ph ze ps si `] mu `] ka
                  .= la [` rh [` et ps ze ph si `] mu `] ka $=
    ( lofdf-juxt lofdf-encl lofdf-void lofcmmbx lofsubb1 ) FCAJDJBJEJKJGJFCBJDJ
    AJEJKJGJLLHIABCDEFGMN $.
    $( [25-Feb-2017] $)

  ${
    lofquadbx.1 $e |- ph .= ps $.
    lofquadbx.2 $e |- ch .= th $.
    $( Double substitution into a bounded and extended form.  (Contributed by
       naipmoro, 3-Sep-2015.) $)
    lofquadbx $p |- rh [` et ph ze ch si `] mu .= rh [` et ps ze th si `] mu $=
      ( lofdf-juxt lofquad lofins lofsubb1 ) AFLCLBFLDLEGHIACBDFABCDJKMNO $.
      $( [3-Sep-2015] $)
  $}

$(
  -----------------------------------------------------------------------------
                                 7. Axioms of LoF
  -----------------------------------------------------------------------------

  [Naip] discusses different sets of axioms for LoF.  Here I adopt the original
  set of [Spencer-Brown] p. 28.  The descriptive names of axioms and theorems
  are Spencer-Brown's own.
$)

  $( J1. Position. $)
  lofj1 $a |- [` [` ph `] ph `] .= $.

  $( J2. Transposition. $)
  lofj2 $a |- [` [` ph ch `] [` ps ch `] `] .= [` [` ph `] [` ps `] `] ch $.

$(
  -----------------------------------------------------------------------------
                                8. Theorems of LoF
  -----------------------------------------------------------------------------

  These theorems, which Spencer-Brown calls Consequences, are from
  [Spencer-Brown] pp. 28-35.  I alter the sequence slightly, proving C5 prior
  to C4. 
$)

  $( C1. Reflexion.  (Contributed by naipmoro, 20-Feb-2017.) $)
  lofc1 $p |- [` [` ph `] `] .= ph $=
    ( lofdf-encl lofdf-juxt lofj1 lofcmmbx lofsub lofsym lofj2 lofeuc lofrepbxs
    lofdf-void lofquadbx loftrans ) ABZBZOACBZNACBZCBZAOAOCBZBRONCBZKKSKKONDZNO
    CBZTKSKKONOKKKKKEOTOCZUBSCBUCOTKOUAFGNAOHIJJSPKQKKKKKAOKKKKKEQKADGLMROBOCBZ
    ACAONAHUDKAODFMM $.
    $( [20-Feb-2017] $)

  $( C2. Generation.  (Contributed by naipmoro, 6-Sep-2015.) $)
  lofc2 $p |- [` ph ps `] ps .= [` ph `] ps $=
    ( lofdf-encl lofdf-juxt lofj2 lofdf-void lofc1 lofquadbx loftrans lofsubb1
    lofj1 lofeucr ) ACZBDZCZBCZBDCZDCZABDCBDZNRMCZPCZDCBDSMPBETAUABFFFFBAGBGHIR
    OCNQFOFFFBKJNGIL $.
    $( [6-Sep-2015] $)

  $( C3. Integration.  (Contributed by naipmoro, 6-Sep-2015.) $)
  lofc3 $p |- [` `] ph .= [` `] $=
    ( lofdf-encl lofdf-juxt lofdf-void lofc2 lofc1 lofj1 lofbeq lofeucr ) ABACZ
    DBZACKDAEJBZBJKJFLDAGHII $.
    $( [6-Sep-2015] $)

  $( C5. Iteration.  (Contributed by naipmoro, 6-Sep-2015.) $)
  lofc5 $p |- ph ph .= ph $=
    ( lofdf-encl lofdf-juxt lofc2 lofdf-void lofc1 lofsubst loftrans lofeucr
    lofj1 ) ABZACBZACZAACZAMKBZACNKADOAEAAFGHLEEAAJGI $.
    $( [6-Sep-2015] $)

  $( C4. Occultation.  (Contributed by naipmoro, 6-Sep-2015.) $)
  lofc4 $p |- [` [` ph `] ps `] ph .= ph $=
    ( lofdf-encl lofdf-juxt lofdf-void lofj2 lofc1 lofsubb1 lofc5 lofeucr lofc3
    loftrans lofsubst ) ACZBDCADZECZCZADZAOPBCZCZDZCADZRONSADCZDCZUBAADZCZUCDCZ
    OUDUGNTDCADOASAFTBNEEABGHLUFNEUCEEUEAEEEEAIHHJESAFLUAPEEEATKHLQEEAEGML $.
    $( [6-Sep-2015] $)

  $( C4 corollary.  (Contributed by naipmoro, 18-Sep-2015.) $)
  lofc4cor $p |- [` ph ps `] [` ph `] .= [` ph `] $=
    ( lofdf-encl lofdf-juxt lofdf-void lofc1 lofsubb1 lofc4 lofeucr ) ACZCZBDCJ
    DABDCJDJKAEBEJAFGJBHI $.
    $( [18-Sep-2015] $)

  $( C6. Extension.  (Contributed by naipmoro, 6-Sep-2015.) $)
  lofc6 $p |- [` [` ph `] [` ps `] `] [` [` ph `] ps `] .= ph $=
    ( lofdf-encl lofdf-juxt lofc1 lofdf-void lofcmmbx lofquadbx loftrans lofbeq
    lofj2 lofj1 lofsubb1 lofeucr ) ACZBCZDCZOBDCZDZOCZASCZCZSTSEUBPCPDCZODZCTUA
    UDUAPODCZBODCZDCUDQUERUFFFFFFOPFFFFFGOBFFFFFGHPBOKIJUCFFOFFPLMINAEI $.
    $( [6-Sep-2015] $)

  $( C6 corollary.  (Contributed by naipmoro, 14-Feb-2017.) $)
  lofc6cor $p |- [` [` ph `] ps `] [` ph ps `] .= [` ps `] $=
    ( lofdf-juxt lofdf-void lofdf-encl lofcmm lofc1 lofc6 lofrepbx ) BACZABCDDA
    EZBCZEDBEZBAFBKCZLDDDJEMBKFMEZBDANEDMBGZOBDKDOACEMPMAHIIII $.
    $( [14-Feb-2017] $)

  $( C7. Echelon.  (Contributed by naipmoro, 6-Sep-2015.) $)
  lofc7 $p |- [` [` [` ph `] ps `] ch `] .= [` ph ch `] [` [` ps `] ch `] $=
    ( lofdf-juxt lofdf-encl lofj2 lofbeq lofdf-void lofsubb1 loftrans lofeucr
    lofc1 ) ACDEBEZCDEDZEZEZAEZBDECDZEZNPQMEZDECDZESOUAAMCFGUARTBQHHCBLIGJNLK
    $.
    $( [6-Sep-2015] $)

  $( C8. Modified transposition.  (Contributed by naipmoro, 6-Sep-2015.) $)
  lofc8 $p |- [` [` ph `] [` ps th `] [` ch th `] `] 
             .= [` [` ph `] [` ps `] [` ch `] `] [` [` ph `] [` th `] `] $=
    ( lofdf-encl lofdf-juxt lofc1 lofj2 lofbeq lofsubb2 lofrepbx lofc7 lofcmmbx
    lofdf-void lofquad loftrans ) AEZBDFEZFCDFEZFEBEZCEZFZEDFZEZQFEZQTFUAFEZQDE
    ZFEZFZRSFZEZEZUJQNNNUEUJGULUDQNNNUKUCBCDHIJKUEUBQFEZUGQFEZFUIUBDQLUMUFUNUHU
    BQNNNNNMUGQNNNNNMOPP $.
    $( [6-Sep-2015] $)

  $( C9. Crosstransposition.  (Contributed by naipmoro, 6-Sep-2015.) $)
  lofc9 $p |- [` [` [` ps `] [` ph `] `] [` [` ch `] [` ph `] `]
             [` [` th `] ph `] [` [` ta `] ph `] `]
             .= [` [` ph `] ps ch `] [` ph th ta `] $=
    ( lofdf-encl lofdf-juxt lofdf-void lofc1 lofquadbx loftrans lofbeq lofsubb2
    lofj2 lofeucr lofc8 lofsubb1 lofc2 lofcmmbx lofc6 ) BFZAFZGFZCFZUBGFZGZDFZA
    GFZGEFZAGFZGFDEGZFZAGZFZUCGUEGFZUBBGCGFZADGEGFZGZUHUJGZUNUFHHHUSFZFUSUNUSIU
    TUMUTUGFZUIFZGFAGUMUGUIANVADVBEHHHHADIEIJKLOMUOUNBGCGZFZUKAGFZGZURUOVDULFZA
    GZFGZVFUOVDUNAGZFGZVIUOVDUNUBFZGFZGZVKUOUNUAFZGUDFZGFVMGVNUMUAUDUBPVOBVPCUN
    HHHVMBICIJKVLAUNHVDHAIZQKVJVHHHVDHULARQKVGUKHAVDHUKIQKVCVEGFVEGZVFURVCVERVR
    AULGFZBGCGZUQGFVEGZURUNVSVEUQHBCGZHHVEULAHHHHHSUKAHHHHHSJVLULGFZBGCGZVLDGEG
    FZGFVEGZWAURWDVTWEUQHHHHVEVLAHULHWBVQQVLAHUKHHVQQJWFWCWEGZBGCGFVEGZURWBWEWC
    HHHVESWHUPVEGURWGUBHWBHVEUBUKTQUKAHHHUPHSKKOKOKK $.
    $( [6-Sep-2015] $)

  $( The following two equations constitute the entire "arithmetic" which
     underlies the Primary Algebra.  LoF (and propositional logic) is nothing
     but a prolonged deduction from this duo, so conceptually they belong at
     the beginning. $)

  $( Intial I1.  Number.  (Contributed by naipmoro, 14-Feb-2017.) $)
  lofi1 $p |- [` `] [` `] .= [` `] $=
    ( lofdf-void lofdf-encl lofc5 ) ABC $.
    $( [14-Feb-2017] $)

  $( Intial I2.  Order.  (Contributed by naipmoro, 14-Feb-2017.) $)
  lofi2 $p |- [` [` `] `] .= $=
    ( lofdf-void lofj1 ) AB $.
    $( [14-Feb-2017] $)

$(
  -----------------------------------------------------------------------------
                      9. Generalizations of LoF consequences
  -----------------------------------------------------------------------------

  This section is a modest start to ease the pain of calculating with LoF in a
  one-dimensional notation.  In generalizing some major theorems, it attempts
  to lighten the significant overhead of commutative term rearrangements and
  maintenance of equational symmetries.  The ugliness of the section is a gauge
  of how inappropriate a linear script is to LoF.
$)

  $( Generalizations of C1. $)

  $( ~ lofc1 reversed.  (Contributed by naipmoro, 14-Feb-2017.) $)
  lofc1r $p |- ph .= [` [` ph `] `] $=
    ( lofdf-encl lofc1 lofsym ) ABBAACD $.
    $( [14-Feb-2017] $)
    
  $( ~ lofc1 extended.  (Contributed by naipmoro, 14-Feb-2017.) $)
  lofc1x $p |- et [` [` ph `] `] ze .= et ph ze $=
    ( lofdf-encl lofc1 lofsubst ) ADDABCAEF $.
    $( [14-Feb-2017] $)
    
  $( ~ lofc1 reversed and extended.  (Contributed by naipmoro, 14-Feb-2017.) $)
  lofc1rx $p |- et ph ze .= et [` [` ph `] `] ze $=
    ( lofdf-encl lofc1r lofsubst ) AADDBCAEF $.
    $( [14-Feb-2017] $)
    
  $( ~ lofc1 bounded and extended.  (Contributed by naipmoro, 14-Feb-2017.) $)
  lofc1bx $p |- si [` et [` [` ph `] `] ze `] rh .= si [` et ph ze `] rh $=
    ( lofdf-encl lofdf-juxt lofdf-void lofc1x lofsubb1 ) BAFFGCGBAGCGHHDEABCIJ
    $.
    $( [14-Feb-2017] $)
    
  $( ~ lofc1 reversed, bounded, and extended.  (Contributed by naipmoro,
     14-Feb-2017.) $)
  lofc1rbx $p |- si [` et ph ze `] rh .= si [` et [` [` ph `] `] ze `] rh $=
    ( lofdf-encl lofdf-juxt lofc1bx lofsym ) DBAFFGCGFGEGDBAGCGFGEGABCDEHI $.
    $( [14-Feb-2017] $)

  $( Generalizations of C2. $)

  $( ~ lofc2 extended.  (Contributed by naipmoro, 14-Feb-2017.) $)
  lofc2x $p |- et [` ph ps ze `] si ps rh .= et [` ph ze `] si ps rh $=
    ( lofdf-juxt lofdf-encl lofcmm lofdf-void lofcmmbx lofcmmx loftrans lofsym
    lofc2 lofrep ) CADGZHZGZEGBGFGCABGDGHGEGBGFGZBEGEBGZSFTBEIQBGHZBGRBGCEFGTQB
    OTCUBGZBGEGFGZTUCEGBGFGUDBDAJJCUAFGKEBUCJFLMNPPN $.
    $( [14-Feb-2017] $)
    
  $( ~ lofc2 bounded and extended.  (Contributed by naipmoro, 14-Feb-2017.) $)
  lofc2bx $p |- mu [` et [` ph ps ze `] si ps rh `] la
                .= mu [` et [` ph ze `] si ps rh `] la $=
    ( lofdf-juxt lofdf-encl lofdf-void lofc2x lofsubb1 ) CABIDIJIEIBIFICADIJIEI
    BIFIKKGHABCDEFLM $.
    $( [14-Feb-2017] $)
    
  $( ~ lofc2 reversed and extended.  (Contributed by naipmoro, 14-Feb-2017.) $)
  lofc2rx $p |- et ps ze [` ph ps si `] rh .= et ps ze [` ph si `] rh $=
    ( lofdf-juxt lofdf-encl lofdf-void lofcmmx lofc2x loftrans ) CBGDGZABGEGHZG
    FGZCAEGHZGBGDGFGZMPGFGOCNGBGDGFGQBDGZNCIFJABCEIDFGKLPRCIFJL $.
    $( [14-Feb-2017] $)
    
  $( ~ lofc2 reversed, bounded, and extended.  (Contributed by naipmoro,
     14-Feb-2017.) $)
  lofc2rbx $p |- mu [` et [` ph ze `] si ps rh `] la
                 .= mu [` et [` ph ps ze `] si ps rh `] la $=
    ( lofdf-juxt lofdf-encl lofc2bx lofsym ) GCABIDIJIEIBIFIJIHIGCADIJIEIBIFIJI
    HIABCDEFGHKL $.
    $( [14-Feb-2017] $)
    
  $( ~ lofc2 special case.  (Contributed by naipmoro, 14-Feb-2017.) $)
  lofc2e $p |- et [` ph `] ze ph si .= [` `] $=
    ( lofdf-encl lofdf-juxt lofdf-void lofc2x lofcmmx lofc3 loftrans ) BAEFCFAF
    DFBGEZFCFAFDFZLGABGCDHMLBFCFAFDFLBLGGCAFDFIBCFAFDFJKK $.
    $( [14-Feb-2017] $)

  $( Generalizations of C3. $)

  $( ~ lofc3 extended.  (Contributed by naipmoro, 14-Feb-2017.) $)
  lofc3x $p |- ph [` `] ps .= [` `] $=
    ( lofdf-void lofdf-encl lofdf-juxt lofcmm lofc3 loftrans ) ACDZEBEIBEZAEIAJ
    FBAEGH $.
    $( [14-Feb-2017] $)
    
  $( ~ lofc3 bounded and extended.  (Contributed by naipmoro, 14-Feb-2017.) $)
  lofc3bx $p |- et [` ph [` `] ps `] ze .= et ze $=
    ( lofdf-void lofdf-encl lofdf-juxt lofc3x lofsubb1 lofc1x loftrans ) CAEFZG
    BGZFGDGCLFGDGCDGMLEECDABHIECDJK $.
    $( [14-Feb-2017] $)

  $( Generalizations of C4. $)

  $( ~ lofc4 extended.  (Contributed by naipmoro, 14-Feb-2017.) $)
  lofc4x $p |- si [` et [` ph `] ze `] rh ph mu .= si ph rh mu $=
    ( lofdf-encl lofdf-juxt lofcmmbx lofcmmx loftrans lofc4 lofid lofrep lofeuc
    lofdf-void ) DBAGZHCHGHEHAHFHZDQBHCHGZHZAHEHFHZDAHEHFHRTEHAHFHUABQPPCDEAHFH
    IEATPFJKSAHADEFHUAABCHLUAMNO $.
    $( [14-Feb-2017] $)
    
  $( ~ lofc4 reversed and extended.  (Contributed by naipmoro, 14-Feb-2017.) $)
  lofc4rx $p |- si ph rh mu .= si [` et [` ph `] ze `] rh ph mu $=
    ( lofdf-encl lofdf-juxt lofc4x lofsym ) DBAGHCHGHEHAHFHDAHEHFHABCDEFIJ $.
    $( [14-Feb-2017] $)

  $( Generalizations of C5. $)

  $( ~ lofc5 extended.  (Contributed by naipmoro, 14-Feb-2017.) $)
  lofc5x $p |- et ph ze ph si .= et ph ze si $=
    ( lofdf-juxt lofdf-void lofcmmx lofc5 lofid lofrep lofeuc ) BAEZCEZAEDELAEC
    EDEZMDECALFDGAAEABCDENAHNIJK $.
    $( [14-Feb-2017] $)

  $( ~ lofc5 bounded and extended.  (Contributed by naipmoro, 25-Feb-2017.) $)
  lofc5bx $p |- rh [` et ph ze ph si `] mu .= rh [` et ph ze si `] mu $=
    ( lofdf-juxt lofdf-void lofc5x lofsubb1 ) BAGCGZAGDGKDGHHEFABCDIJ $.
    $( [25-Feb-2017] $)

    
  $( ~ lofc5 reversed and extended.  (Contributed by naipmoro, 14-Feb-2017.) $)
  lofc5rx $p |- et ph ze si .= et ph ze ph si $=
    ( lofdf-juxt lofc5x lofsym ) BAECEZAEDEHDEABCDFG $.
    $( [14-Feb-2017] $)

  $( Generalizations of C6. $)

  $( ~ lofc6 extended.  (Contributed by naipmoro, 25-Feb-2017.) $)
  lofc6x $p |- et [` [` ph `] [` ps `] `] ze [` [` ph `] ps `] si
               .= et ph ze si $=
    ( lofdf-encl lofdf-juxt lofc6 lofdf-void lofcmmx lofreps ) AFZBFGFZLBGFZGAC
    DEGCMGZDGNGEGABHDNOIEJK $.
    $( [25-Feb-2017] $)

  $( ~ lofc6 reversed and extended.  (Contributed by naipmoro, 25-Feb-2017.) $)
  lofc6rx $p |- et [` [` ph `] ps `] ze [` [` ph `] [` ps `] `] si
                .= et ph ze si  $=
    ( lofdf-encl lofdf-juxt lofcmmx lofc6x loftrans ) CAFZBGFZGDGKBFGFZGEGCMGDG
    LGEGCAGDGEGLMCDEHABCDEIJ $.
    $( [25-Feb-2017] $)

  $( Generalizations of J1. $)

  $( ~ lofj1 extended.  (Contributed by naipmoro, 14-Feb-2017.) $)
  lofj1x $p |- rh [` et [` ph `] ze ph si `] mu .= rh mu $=
    ( lofdf-encl lofdf-juxt lofdf-void lofc2bx lofc3bx loftrans ) EBAGHCHAHDHGH
    FHEBIGHCHAHDHGHFHEFHIABICDEFJBCAHDHEFKL $.
    $( [14-Feb-2017] $)

  $( ~ lofj1 reversed and extended.  (Contributed by naipmoro, 25-Feb-2017.) $)
  lofj1rx $p |- rh [` et ph ze [` ph `] si `] mu .= rh mu $=
    ( lofdf-juxt lofdf-encl lofcmmbx lofj1x loftrans ) EBAGCGAHZGDGHGFGEBLGCGAG
    DGHGFGEFGALBCDEFIABCDEFJK $.
    $( [25-Feb-2017] $)

  $( ~ lofj1 extended and switched.  (Contributed by naipmoro, 14-Feb-2017.) $)
  lofj1xs $p |- rh mu .= rh [` et [` ph `] ze ph si `] mu $=
    ( lofdf-encl lofdf-juxt lofj1x lofsym ) EBAGHCHAHDHGHFHEFHABCDEFIJ $.
    $( [14-Feb-2017] $)

  $( Generalizations of J2. $)

  $( ~ lofj2 extended.  (Contributed by naipmoro, 14-Feb-2017.) $)
  lofj2x $p |- et [` [` ph ch `] [` ps ch `] `] ze si
               .= et [` [` ph `] [` ps `] `] ze ch si $=
    ( lofdf-juxt lofdf-encl lofj2 lofsubst lofdf-void lofcmmx loftrans ) DACGHB
    CGHGHZGEGFGDAHBHGHZGZCGEGFGPEGCGFGNOCGDEFGABCIJCEPKFLM $.
    $( [14-Feb-2017] $)
    
  $( ~ lofj2 reversed and extended.  (Contributed by naipmoro, 14-Feb-2017.) $)
  lofj2rx $p |- et [` [` ph `] [` ps `] `] ze ch si
                .= et [` [` ph ch `] [` ps ch `] `] ze si $=
    ( lofdf-juxt lofdf-encl lofj2x lofsym ) DACGHBCGHGHGEGFGDAHBHGHGEGCGFGABCDE
    FIJ $.
    $( [14-Feb-2017] $)

$(
  -----------------------------------------------------------------------------
                          10. Excursion into equality
  -----------------------------------------------------------------------------
$)

  $( We will later define ` ( ph -> ps ) ` as ` [` ph `] ps `.  This theorem
     shows that our previous definition of equality is equivalent to
     ` ( ( ph -> ps ) /\ ( ps -> ph ) ) ` .  The latter, in turn, is what we
     mean by the biconditional ` <-> ` .  In othe words, equality and the
     biconditional are, as expected, equivalent.  This proof is adapted from
     the proof of ~ bicond in [Naip].  (Contributed by naipmoro, 24-Feb-2017.)
  $)
  lofbiimp $p |- [` [` [` ph `] ps `] [` [` ps `] ph `] `]
                 .= [` [` ph `] [` ps `] `] [` ph ps `] $=
    ( lofdf-encl lofdf-juxt lofdf-void lofcmm lofsubbd1 lofc1 lofsubb1 lofcmmbx
    lofc6 lofc9 lofeucr ) BACZDZCBCZADCZDCZNBDZCQDCNPDCABDCDZOSEEEQEEBNFGPCZNDC
    ZQDZCZRTUABENEQEEBHGECZNDCZUEADCZDZUBDQDCZUDTUHEEUCEEEAKIUFUBDQDUGDCUITUCUG
    UFEEEEJAEPBELMMMM $.
    $( [24-Feb-2017] $)

  $( We next prove that equality, and hence the biconditional, are
     associative.  First, four preliminary theorems. $)

  $( Lemma.  Adapted from the proof of ~ c2lem1 in [Naip].  (Contributed by
     naipmoro, 24-Feb-2017.) $)
  lofbiasslem1 $p |-  [` ps [` ph ps `] ch `] .= [` [` ph `] ps ch `] $=
    ( lofdf-juxt lofdf-encl lofdf-void lofcmmbx lofc2bx loftrans ) BABDEZDCDEJB
    DCDEAEBDCDEBJFFCFFGABFFFCFFHI $.
    $( [24-Feb-2017] $)

  $( Lemma.  Adapted from the proof of ~ c2lem2 in [Naip].  (Contributed by
     naipmoro, 24-Feb-2017.) $)
  lofbiasslem2 $p |-  [` ph [` ph ps `] ch `] .= [` ph [` ps `] ch `] $=
    ( lofdf-juxt lofdf-encl lofdf-void lofcmmbdx lofbiasslem1 loftrans lofcmmbx
    ) AABDEDCDEZBEZADCDEZALDCDEKABADEDCDEMABFFFACFFGBACHILAFFCFFJI $.
    $( [24-Feb-2017] $)

  $( Let ` P .= [` [` ph `] [` ps `] `] [` ph ps `] ` and
         ` Q .= [` [` ps `] [` ch `] `] [` ps ch `] ` .
     Proving that equality/biconditional associates amounts to proving:  
         ` [` [` P `] [` ch `] `] [` P ch `]
        .= [` [` ph `] [` Q `] `] [` ph Q `] `
     which is demonstrated in ~ lofbiass.  Meanwhile, this theorem shows that
     the LHS of the latter equation evaluates to a form symmetric in the three
     variables, informal evidence for associativity.  Adapted from the proof of
     ~ bic3 in [Naip].  (Contributed by naipmoro, 24-Feb-2017.)
          $)
  lofbiass3 $p |- [` [` [` [` ph `] [` ps `] `] [` ph ps `] `] [` ch `] `]
                  [` [` [` ph `] [` ps `] `] [` ph ps `] ch `]
                  .= [` [` ph `] [` ps `] [` ch `] `] [` ph ps [` ch `] `]
                     [` ph [` ps `] ch `] [` [` ph `] ps ch `] $=
    ( lofdf-encl lofdf-juxt lofj2 lofbeq lofeucr lofbiasslem2 lofsubst loftrans
    lofc1 lofquad lofbiasslem1 lofsubr ) ADZBDZEZDABEZDZEZDCDZEZDZUACEZDZEZRUBE
    DSUBEDEZAQECEDZEZBTECEDZEUJPBECEDZEUGUHATECEDZUKEZEUHUIUKEEUDUHUFUNUHDZDUDU
    HUOUCRSUBFGUHLHUNDZDUFUNUPUEABTCEFGUNLHMUMUIUHUKABCIJKUKULUJABCNOK $.
    $( [24-Feb-2017] $)

  $( A permuted version of ~ lofbiass3 .  Adapted from the proof of ~ bic3x in
     [Naip].  (Contributed by naipmoro, 29-Dec-2016.)  $)
  lofbiass3p $p |- [` [` [` [` ps `] [` ch `] `] [` ps ch `] `] [` ph `] `]
                   [` [` [` ps `] [` ch `] `] [` ps ch `] ph `]
                   .= [` [` ph `] [` ps `] [` ch `] `] [` ph ps [` ch `] `]
                      [` ph [` ps `] ch `] [` [` ph `] ps ch `] $=
    ( lofdf-encl lofdf-juxt lofbiass3 lofdf-void lofcmmbx loftrans lofcmmx ) BD
    ZCDZEZDBCEZDEZDADZEDOAEDEZPKELEDZPBECEDZEZAKECEDZEABELEDZEZRUBEUAESEQTUBEZU
    AEZUCQUDKCEZAEDZEZUEQTBLEZAEDZEUGEZUHQRNPEDZEUJEUGEZUKQMPEDULEUJEUGEUMBCAFM
    PGGGGULUJEUGEHINPGGGRUJUGEHIUIAGGGTUGHIUFAGGGUDGHIUBUATGGJISUBRUAGJI $.
    $( [29-Dec-2016] $)

  $( Proving the associativity of equality/biconditional.   Adapted from the
     proof of ~ bicond-assc in [Naip].  (Contributed by naipmoro, 29-Dec-2016.)
  $)
  lofbiass  $p |- [` [` [` [` ph `] [` ps `] `] [` ph ps `] `] [` ch `] `]
                  [` [` [` ph `] [` ps `] `] [` ph ps `] ch `]
                  .= [` [` ph `] [` [` [` ps `] [` ch `] `] [` ps ch `] `] `]
                     [` ph [` [` ps `] [` ch `] `] [` ps ch `] `] $=
    ( lofdf-encl lofdf-juxt lofbiass3 lofbiass3p lofdf-void lofcmmbx loftrans
    lofeuc ) ADZBDZEZDABEZDEZDCDZEDPCEDEZMQEDZBCEDZEZDZLEDUAAEDZEZLUBEDZASETEDE
    ZRNQEDOQEDEAMECEDELBECEDEUDABCFABCGKUDUEUCEUFUBLHHHHUCIUAAHHHUEHIJJ $.
    $( [29-Dec-2016] $)

$(
  -----------------------------------------------------------------------------
                        11. Implementing LoF deduction
  -----------------------------------------------------------------------------
$)

  $( This key theorem states that the equivalence of ` ph ` to True is
     equivalent to just ` ph ` .  (Contributed by naipmoro, 29-Jan-2017.) $)
  lofelimeq $p |- [` [` ph `] [` [` `] `] `] [` ph [` `] `] .= ph $=
    ( lofdf-encl lofdf-void lofi2 lofsubb1 lofc1 lofsubst loftrans lofcmm lofc2
    lofdf-juxt lofcmmbx ) ABZCBZBZKBANKBZKZOAKZAQNAKBZAKZRQASKZTQAPKZUAQMBZPKUB
    OCMCCPDEUCACPAFGHANCCCACLHASIHNAJHOCCADGH $.
    $( [29-Jan-2017] $)

  $( The LoF deduction axiom.  This axiom is the key that allows us to
     interchange equational and classical forms.  $)
  ${
    lofax-ded.1 $e |- ph $.
    lofax-ded.2 $e |- ph .= ps $.
    $( If we assert both ` ph ` and that ` ph ` is equal to ` ps ` , we can
       assert ` ps ` .  (Contributed by naipmoro, 14-Feb-2017.) $)
    lofax-ded $a |- ps $.
  $}

  $( Truth equivalence elimination.  $)
  ${
    lofelim.1 $e |- ph .= [` `] $.
    $( If ` ph ` is equivalent to True, we can assert ` ph ` .  (Contributed by
       naipmoro, 14-Feb-2017.) $)
    lofelim $p |- ph $=
      ( lofdf-encl lofdf-void lofdf-juxt lofdf-equ lofelimeq lofax-ded ) ACDCZC
      ECAIECEAAIBFAGH $.
      $( [14-Feb-2017] $)
  $}

  $( Truth equivalence introduction.  $)
  ${
    lofintr.1 $e |- ph $.
    $( If we can assert ` ph ` , then we can assert that ` ph ` is equivalent
       to True.  (Contributed by naipmoro, 14-Feb-2017.) $)
    lofintr $p |- ph .= [` `] $=
      ( lofdf-void lofdf-encl lofdf-juxt lofelimeq lofsym lofax-ded lofdf-uni )
      ACDZAADJDEDAJEDEZBKAAFGHI $.
      $( [14-Feb-2017] $)
  $}

  ${
    lofeucrelim.1 $e |- ph .= ps $.
    lofeucrelim.2 $e |- ph .= [` `] $.
    $( Eliminate equation from ~ lofeucr deduction.  (Contributed by naipmoro,
       14-Feb-2017.) $)
    lofeucrelim $p |- ps $=
      ( lofdf-void lofdf-encl lofeucr lofelim ) BABEFCDGH $.
      $( [14-Feb-2017] $)
  $}

  ${
    loftranselim.1 $e |- ph .= ps $.
    loftranselim.2 $e |- ps .= [` `] $.
    $( Eliminate equation from ~ loftrans deduction.  (Contributed by naipmoro,
       14-Feb-2017.) $)
    loftranselim $p |- ph $=
      ( lofdf-void lofdf-encl loftrans lofelim ) AABEFCDGH $.
      $( [14-Feb-2017] $)
  $}

  ${
    lofand.1 $e |- ph $.
    lofand.2 $e |- ps $.
    $( Wrap premises in LoF conjunctive form.  From ` ph ` and `ps ` we can
       conclude the LoF equivalent of ` ph /\ ps ` . (Contributed by naipmoro,
       14-Feb-2017.) $)
    lofand $p |- [` [` ph `] [` ps `] `] $=
      ( lofdf-encl lofdf-juxt lofc3bx lofintr lofeuc lofdf-equ lofrepbx lofeucr
      lofdf-void lofelim ) AEBEFEZOMEZBFEFOPMBOMGAPMBOMPACHZOABFEFABAPBQBDHIJHK
      LN $.
      $( [14-Feb-2017] $)
  $}

  ${
    lofeq.1 $e |- ph $.
    lofeq.2 $e |- ps $.
    $( From assertions of ` ph ` and ` ps ` we can assert their equality.
       (Contributed by naipmoro, 21-Feb-2017.) $)
    lofeq $p |- ph .= ps $=
    wph lofdf-void lofdf-encl wps
    wph lofeq.1 lofintr
    wps lofeq.2 lofintr
    lofeuc
    $.
  $}

  ${
    lofmp.1 $e |- ph $.
    lofmp.2 $e |- [` ph `] ps $.
    $( LoF version of modus ponens.  (Contributed by naipmoro, 14-Feb-2017.) $)
    lofmp $p |- ps $=
      ( lofdf-encl lofdf-void lofintr lofbeq loftrans lofdf-juxt lofrep lofelim
      lofc1 ) BAEZFFBFEZNOEFAOACGHFMINBJDGKL $.
      $( [14-Feb-2017] $)
  $}

$(
  -----------------------------------------------------------------------------
                   12. Defining classical propositional logic
  -----------------------------------------------------------------------------

  We define ` ( ph -> ps ) ` as ` [` ph `] ps ` and ` -. ph ` as ` [` ph `] ` .
  Constructing hybrid wffs like ` [` -. ph `] ` that lack meaning in either LoF
  or propositional logic becomes not merely possible but necessary in the
  course of translating from one system to the other.  Indeed, one can validly
  calculate with these hybrid forms.  For example, ` [` -. ph `] -. ph ` can
  be reduced to ` [` `] ` by ~ lofc2e without the need to fully translate into
  LoF.  
$)

  $( Declare the primitive constant symbols for propositional calculus. $)
  $c ( $.  $( Left parenthesis $)
  $c ) $.  $( Right parenthesis $)
  $c -> $. $( Right arrow (read:  "implies") $)
  $c -. $. $( Right handle (read:  "not") $)

  $( Classical material implication is a wff. $)
  wi $a wff ( ph -> ps ) $.
  
  $( Classical negation is a wff. $)
  wn $a wff -. ph $.

  $( Define material implication in terms of LoF. $)
  lofdf-imp $a |- ( ph -> ps ) .= [` ph `] ps $.

  $( Define negation in terms of LoF. $)
  lofdf-neg $a |- -. ph .= [` ph `] $.

$(
  -----------------------------------------------------------------------------
                         13.  Hybrid theorems
  -----------------------------------------------------------------------------
$)

  lofne $p |- [` -. ph `] .= ph $=
    wph wn lofdf-encl
    wph lofdf-encl lofdf-encl
    wph
    wph wn  wph lofdf-encl
    wph lofdf-neg
    lofbeq
    wph lofc1
    loftrans 
    $.

 

$(
  -----------------------------------------------------------------------------
                  14.  Propositional logic is superfluous
  -----------------------------------------------------------------------------

  From this point on, we can prove all the true statements of propositional
  logic (axioms and theorems) entirely in LoF and translate the results back 
  into propositional form.  Below is an example where I prove Principia
  Mathematica's "proof by contradiction" theorem known as the Law of Clavius
  [WhiteheadRussell] p. 103.

  From the point of view of LoF, the Law of Clavius, like most theorems of
  propositional logic, is a trivial truth undeserving of the label "theorem".
  It would be as though someone claimed that "3x - 2x = x" was a "theorem" of
  numerical algebra.  Technically, yes ...

  One day LoF will supplant the propositional calculus, as inevitably as brute
  algebraic computations (mostly) supplanted elegant geometric reasoning, and
  for much the same reasons.  But not in the manner shown here.  If you examine
  the proof below, you will appreciate all the overhead involved in translating
  back and forth between the two systems.  Until predicate logic itself is
  conquered by boundary formalism, and a single logic is deployed, one should
  not expect much movement on the part of logicians.
$)

  $( LoF version of metamath's ~ pm2.18.  (Contributed by naipmoro,
     14-Feb-2017.) $)
  lofpm2.18 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wn wi lofdf-encl lofdf-juxt lofdf-neg lofdf-imp lofrepbxs lofc2x loftrans
    lofdf-void lofc1x lofreps lofc2e lofelim ) ABZACZACZRADZAEKDPSKARAFRPDZAEZD
    AEZPAEZQUAKKKARPAGQAGHUBTDAEUCTAKKKKIPKALJJMAKKKNJO $.
    $( [14-Feb-2017] $)

$(
  -----------------------------------------------------------------------------
               15.  Proving the axioms of propositional logic
  ----------------------------------------------------------------------------- 
$)

  $( Derive metamath's axiom ~ ax-1 as a theorem.  (Contributed by naipmoro,
     14-Feb-2017.) $)
  ax-1 $p |- ( ph -> ( ps -> ph ) ) $=
    ( wi lofdf-encl lofdf-juxt lofdf-void lofdf-imp lofsubr loftrans lofelim
    lofc2e ) ABACZCZMADZBDZEAEZFDMNLEPALGLOAENBAGHIAFOFKIJ $.
    $( [14-Feb-2017] $)
    
  $( Derive metamath's axiom ~ ax-2 as a theorem.  (Contributed by naipmoro,
     14-Feb-2017.) $)
  ax-2 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    ( lofdf-encl lofdf-juxt lofdf-imp lofreps lofrepbxs lofc2x loftrans lofcmmx
    wi lofdf-void lofc2e lofelim ) ABCLZLZABLZACLZLZLZUAADZBDZECEZDZUBEUCECEZMD
    UAUEUCEUBECEZUFUAUEUBBEZDZEUBECEUGPUCCEUBMMUIUBECEZUABCFQUBPEMMMUJUAAPFRUHM
    MQDZUBCEZUAABFSULUKRDZEMUAACFTUMSEUKMUARSFQTFGGHHHMUBUEBMCIJUCUBUEMCKJUDMMM
    NJO $.
    $( [14-Feb-2017] $)
    
  $( Derive metamath's axiom ~ ax-3 as a theorem.  (Contributed by naipmoro,
     14-Feb-2017.) $)
  ax-3 $p |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) )
       $=
    ( wn wi lofdf-encl lofdf-juxt lofdf-void lofdf-neg lofbeq lofdf-imp lofreps
    lofrepbxs lofc2x loftrans lofc1bx lofc2e lofelim ) ACZBCZDZBADZDZUBAEZBEZFA
    FZGEUBUCEZEUDFAFZUEUBUFUDFEUDFAFUGSUDUFGGUDAFZUBBHREZUFGSGUHUBRUCAHITUISFGG
    GUHUBRSJUAUHTEGUBBAJTUAJKLLLUFUDGGGAMNAGGGUHONAGUDGPNQ $.
    $( [14-Feb-2017] $)

  ${
    $( Minor premise for modus ponens. $)
    min $e |- ph $.
    $( Major premise for modus ponens. $)
    maj $e |- ( ph -> ps ) $.
    $( Derive metamath's modus ponens ~ ax-mp as a theorem.  (Contributed by
       naipmoro, 14-Feb-2017.) $)
    ax-mp $p |- ps $=
      ( lofdf-encl lofdf-juxt wi lofdf-void lofdf-imp lofintr lofeucr lofelim
      lofmp ) ABCAEBFZABGZNHEABIODJKLM $.
      $( [14-Feb-2017] $)
  $}

$(
  -----------------------------------------------------------------------------
                                16.  Conclusion
  -----------------------------------------------------------------------------

  With the proofs of ~ ax-1 , ~ ax-2 , ~ ax-3 , and ~ ax-mp completed, we can
  retire LoF and proceed with the normal development of metamath's logic.
  Although one could always descend, here or there, back into LoF, it is hard
  to imagine many scenarios where that would be useful.

  This file has been tested with the master branch version of set.mm
  (https://github.com/metamath/set.mm/blob/master/set.mm  as of commit
   558ed611a8d20ccdf7d486f19ad86c76bbab59e0 on 20-Dec-2016).

  To test this file, remove (or comment out) the following sections of set.mm:
  * Pre-logic
  * Recursively define primitive wffs for propositional calculus
  * The axioms of propositional calculus

  Paste the contents of this file anywhere before the start of set.mm's active
  statements. Read the ensuing (saved) file into metamath and run "verify
  proof *".  Expected result: "All proofs in the database were verified."

  An example of such an altered set.mm file is available here:
  https://github.com/naipmoro/lofmm/blob/master/set(lof).mm .
$)

$(
  -----------------------------------------------------------------------------
                            17.  The biconditional
  ----------------------------------------------------------------------------- 
$)

  $( Declare the biconditional symbol. $)
  $c <-> $.

  $( The biconditional is a wff. $)
  wb $a wff ( ph <-> ps ) $.

  $( A definition of the biconditional in terms of LoF equality.  (Contributed
     by naipmoro, 21-Feb-2017.) $)
  lofdf-bi $a |- ( ph <-> ps ) .= [` [` ph `] [` ps `] `] [` ph ps `] $.

  $( We demonstrate a more traditional understanding of the biconditional as a
     conjunction of an implication and its converse.  (Contributed by naipmoro,
     24-Feb-2017.) $)
  lofdfbiimp $p |- ( ph <-> ps )
                   .= [` [` [` ph `] ps `] [` [` ps `] ph `] `] $=
    ( wb lofdf-encl lofdf-juxt lofdf-bi lofbiimp lofeuc ) ABCADZBDZEDABEDEIBEDJ
    AEDEDABFABGH $.
    $( [24-Feb-2017] $)

  $( Lemma for dfbi1.  (Contributed by naipmoro, 25-Feb-2017.) $)
  lofdfbi1lem1 $p |-  -. ( ( ph -> ps ) -> -. ( ps -> ph ) )
                      .= [` [` [` ph `] ps `] [` [` ps `] ph `] `] $=
    ( wi lofdf-encl lofdf-juxt lofdf-neg lofdf-void lofdf-imp lofsubb1 loftrans
    wn lofsubbd1 ) ABCZBACZKZCZKZADBEZDZNDZEDZSBDAEZDEDQMDZTEDZUAQUCOEZDZUDQPDU
    FPFPUEGGGGMOHIJOTUCGGGNFIJMRGGGTGGABHLJNUBGGSGGGBAHLJ $.
    $( [25-Feb-2017] $)

  $( Lemma for dfbi1.  (Contributed by naipmoro, 25-Feb-2017.) $)
  lofdfbi1lem2 $p |- -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) .= ( ph <-> ps ) $=
    ( wi wn lofdf-encl lofdf-juxt wb lofdfbi1lem1 lofdfbiimp lofeuc ) ABCBACDCD
    AEBFEBEAFEFEABGABHABIJ $.
    $( [25-Feb-2017] $)

  ${
    lofbieq.1 $e |- ( ph <-> ps ) $.
    $( Deducing an equality from a biconditional.  (Contributed by naipmoro,
       24-Feb-2017.) $)
    lofbieq   $p |- ph .= ps $=
      ( wb lofdf-encl lofdf-juxt lofdf-bi lofax-ded lofdf-uni ) ABABDAEBEFEABFE
      FCABGHI $.
      $( [24-Feb-2017] $)
  $}  

  $( Property of the biconditional connective.  (Contributed by naipmoro,
     24-Feb-2017.) $)
  bi1 $p |- ( ( ph <-> ps ) -> ( ph -> ps ) ) $=
    ( wb wi lofdf-encl lofdf-juxt lofdf-void lofj1rx lofdf-bi lofdf-imp lofreps
    lofrepbxs lofj2rx loftrans lofc1x lofc2e lofelim ) ABCZABDZDZTAEZBEFZUAFZBF
    ZGETUCEZEBFUDABFZUAFEZGUEGGBTAGBGGGHTUBEUFEFZEUAFBFUEUGFEBFRUHGGGUABFZTABIS
    UIREGTABJRSJKLUBUFUAGGBMNLUCGBONBUAUAGPNQ $.
    $( [24-Feb-2017] $)

  $( Property of the biconditional connective.  (Contributed by naipmoro,
     24-Feb-2017.) $)
  bi3 $p |-  ( ( ph -> ps ) -> ( ( ps -> ph ) -> ( ph <-> ps ) ) )  $=
    ( wi wb lofdf-encl lofdf-juxt lofdf-void lofsubr loftrans lofdf-bi lofsubb1
    lofdf-imp lofc6rx lofc2rx lofcmm lofc2e lofelim ) ABCZBACZABDZCZCZUBBEZAFZE
    ZUCFZAFZGEUBAUEFZUCFZUGUBUHABFEZFZUIUBAEZBFZEZUEFULUCFEUJFZFZUKUBUNSEZFUOFZ
    UPUBREZUQFZUOFZURUBUTTFZVAUBUSUAFVBRUALUAUQTFUSSTLHITUOUTABJHIRUMGGGUQUOFAB
    LKISUDGGUNUOBALKIABGUEUJMIGAGUEBGNIAUFOIUDGGGPIQ $.
    $( [24-Feb-2017] $)

  

  $( Relate the biconditional connective to primitive connectives.  
     (Contributed by naipmoro, 25-Feb-2017.) $)
  dfbi1 $p |- ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $=
    ( wb wi wn lofdf-encl lofdf-juxt lofdf-void lofdf-bi lofdfbi1lem2 lofsubbd1
    loftrans lofsubb1 lofc5bx lofc2e lofelim ) ABCZABDBADEDEZCZSQFZFZTGZHFSUAQQ
    GFZGZUBSTTGFZUCGZUDSUEQRGFZGZUFSTRFGFUGGUHQRIRQHHTHHUGABJZKLRQQHUEHUIMLTHHH
    HUCNLQHHHUAHNLTHHHOLP $.
    $( [25-Feb-2017] $)

  df-bi $p |- -. ( ( ( ph <-> ps ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )
        -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) )
    $=

    ?
    $.

$(
  -----------------------------------------------------------------------------
                                 REFERENCES
  -----------------------------------------------------------------------------

  1. [Naip] naipmoro, "lof.mm", Metamath file (2015); available at 
     https://github.com/naipmoro/lofmm/blob/master/lof.mm .
  2. [Spencer-Brown] Spencer-Brown, George, "Laws of Form", Allen & Unwin,
     London (1969).
$)

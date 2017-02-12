$(
  lawsofforminset.mm    
  version 0.1.0    
  Copyright (C) 2017 naipmoro

  This file is made available under the MIT License:
  http://opensource.org/licenses/MIT

  This file contains verbatim excerpts from set.mm 
  (found at https://github.com/metamath/set.mm/blob/master/set.mm) which 
  is released under the CC0 1.0 Universal public domain license.
$)

$(
  -----------------------------------------------------------------------------
                               INTRODUCTION
  -----------------------------------------------------------------------------

  In [Moro] I presented metamath derivations of Spencer-Brown's Primary Algebra
  (details of PA can be found in chapter 6 of [Spencer-Brown]).  lof.mm was a 
  stand-alone project that, for reasons of readability, was not written to be 
  compatible with set.mm, metamath's ongoing formalization of mathematics.  
  Here I present a version which is more than just compatible: I end up 
  deriving set.mm's propositional calculus from PA.  There is nothing
  surprising in this -- classical propositional logic is one of the 
  interpretations of PA (Boolean algebra is another).  The real interest lies 
  in the means of derivation.
  
  PA is an equational system while propositional logic is implicational.
  

$)

  $( Declare the primitive constant symbols for the Primary Algebra. $)
  $c `[ $. $( Left bracket $)
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

  $( Axioms ---------------------------------------------------
     In keeping with the spirit of LoF's austerity, I aimed for the most
     minimal formalism possible.  I start with the five constant symbols listed
     above and seven basic axioms: three to provide a recursive definition of
     'form', three common notions (so to speak) to power symbol manipulation,
     and a commutativity axiom.  Metamath does not distinguish definitions from
     proper axioms.
  $)

  $( Recursive definition of LoF form (wff) -----------------------------
     1. Empty space is a wff.
     2. If ` ph ` is a wff, enclosing it in brackets is a wff.
     3. If ` ph ` and ` ps ` are wffs, juxtaposing them is a wff.
  $)

  $( Empty space is a wff. $)
  lofdf-void $a wff $.

  $( If ` ph ` is a wff, then ` `[ ph `] ` is a wff. $)
  lofdf-encl $a wff `[ ph `] $.

  $( If ` ph ` and ` ps ` are wffs, then ` ph ps ` is a wff. $)
  lofdf-juxt $a wff ph ps $.


  $( Common Notions --------------------------------------------
     One goal of lof.mm is exploring the minimal basis for a boundary algebra.
     The next 3 axioms are the required machinery of symbol manipulation.
  $)

  ${
    lofax-euc.1 $e |- `[ `[ ph `] `[ ps `] `] `[ ph ps `] $.
    lofax-euc.2 $e |- `[ `[ ch `] `[ ps `] `] `[ ch ps `] $.
    $( We read this as:  If ` ph ` is equivalent to ` ps ` and ` ch ` is
       equivalent to ` ps ` , then we can assert that ` ph ` is equivalent to
       ` ch ` . $)
    lofax-euc $a |- `[ `[ ph `] `[ ch `] `] `[ ph ch `] $.
  $}

  ${
    lofax-beq.1 $e |- `[ `[ ph `] `[ ps `] `] `[ ph ps `] $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    lofax-beq $a |- `[ `[ `[ ph `] `] `[ `[ ps `] `] `] `[ `[ ph `] `[ ps `] `]
    $.
  $}

  ${
    lofax-sub.1 $e |- `[ `[ ph `] `[ ps `] `] `[ ph ps `] $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    lofax-sub $a |- `[ `[ ph ze `] `[ ps ze `] `] `[ ph ze ps ze `] $.
  $}
  $( PLEASE PUT DESCRIPTION HERE. $)
  lofax-cmm $a |- `[ `[ ph ps `] `[ ps ph `] `] `[ ph ps ps ph `] $.


  $( Theorems -------------------------------------------------------- The
     symbol '=' is never defined but it will turn out to obey the expected laws
     of an equivalence relation.  Specifically, from the common notion that two
     things equal to the same thing are equal to each other and from the
     commutativity of LoF, we derive the reflexivity, symmetry, and
     transitivity of '='.  Note that such a derivation is not possible in a
     traditional formal system without additional axioms -- it is the ability
     to reference the empty (or void) form that allows it here. $)
  lofidu $p |- `[ `[ ph `] `[ ph `] `] `[ ph ph `] $=
    wph lofdf-void lofax-cmm $.
    $( [26-Jan-2017] $)


  ${
    lofsymu.1 $e |- `[ `[ ph `] `[ ps `] `] `[ ph ps `] $.
    $( '=' is symmetric. $)
    lofsymu $p |- `[ `[ ps `] `[ ph `] `] `[ ps ph `] $=
      wps wps wph wps lofidu lofsymu.1 lofax-euc $.
      $( [26-Jan-2017] $)
  $}

  ${
    loftransu.1 $e |- `[ `[ ph `] `[ ps `] `] `[ ph ps `] $.
    loftransu.2 $e |- `[ `[ ps `] `[ ch `] `] `[ ps ch `] $.
    $( '=' is transitive. $)
    loftransu $p |- `[ `[ ph `] `[ ch `] `] `[ ph ch `] $=
      wph wps wch loftransu.1 wps wch loftransu.2 lofsymu lofax-euc $.
      $( [26-Jan-2017] $)
  $}

  $( Introducing the notion of lof equality. $)
  $c `= $.

  ${
    lofdf-NtoU.1 $e |- ph `= ps $.
    $( What equality means in terms of LoF's unitary formalism. $)
    lofdf-NtoU $a |- `[ `[ ph `] `[ ps `] `] `[ ph ps `] $.
  $}

  ${
    lofdf-UtoN.1 $e |- `[ `[ ph `] `[ ps `] `] `[ ph ps `] $.
    $( Translating LoF unitary form into normal form. $)
    lofdf-UtoN $a |- ph `= ps $.
  $}


  ${
    lofeuc.1 $e |- ph `= ps $.
    lofeuc.2 $e |- ch `= ps $.
    $( Two things equal to the same thing are equal to each other.  This is
       Euclid's first Common Notion and, in an equational logic, this and its
       sibling, transitivity, are the main engine of derivation. $)
    lofeuc $p |- ph `= ch $=
      wph wch wph wps wch wph wps lofeuc.1 lofdf-NtoU wch wps lofeuc.2
      lofdf-NtoU lofax-euc lofdf-UtoN $.
      $( [26-Jan-2017] $)
  $}


  ${
    lofbeq.1 $e  |- ph `= ps $.
    $( Enclosing equal forms leaves equal forms. $)
    lofbeq $p |- `[ ph `] `= `[ ps `] $=
      wph lofdf-encl wps lofdf-encl wph wps wph wps lofbeq.1 lofdf-NtoU
      lofax-beq lofdf-UtoN $.
      $( [26-Jan-2017] $)
  $}


  ${
    lofsub.1 $e |- ph `= ps $.
    $( Juxtaposing the same form with equal forms leaves equal forms. $)
    lofsub $p |- ph ze `= ps ze $=
      wph wze lofdf-juxt wps wze lofdf-juxt wph wps wze wph wps lofsub.1
      lofdf-NtoU lofax-sub lofdf-UtoN $.
      $( [26-Jan-2017] $)
  $}

  $( Commutativity of LoF. $)
  lofcmm $p |- ph ps `= ps ph $=
    wph wps lofdf-juxt wps wph lofdf-juxt wph wps lofax-cmm lofdf-UtoN $.
    $( [26-Jan-2017] $)

  $( From the common notion that two
     things equal to the same thing are equal to each other and from the
     commutativity of LoF, we derive the reflexivity, symmetry, and
     transitivity of '='.  Note that such a derivation is not possible in a
     traditional formal system without additional axioms -- it is the ability
     to reference the empty (or void) form that allows it here. $)

  $( ` ` = ` is reflexive. $)
  lofid $p |- ph `= ph $=
    wph lofdf-void lofcmm $.
    $( [6-Sep-2015] $)

  ${
    lofsym.1 $e |- ph `= ps $.
    $( ` ` = ` is symmetric. $)
    lofsym $p |- ps `= ph $=
      wps wps wph wps lofid lofsym.1 lofeuc $.
      $( [2-Sep-2015] $)
  $}

  ${
    loftrans.1 $e |- ph `= ps $.
    loftrans.2 $e |- ps `= ch $.
    $( ` ` = ` is transitive. $)
    loftrans $p |- ph `= ch $=
      wph wps wch loftrans.1 wps wch loftrans.2 lofsym lofeuc $.
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
    lofeucr.1 $e |- ph `= ps $.
    lofeucr.2 $e |- ph `= ch $.
    $( A commuted - or reversed - version of ~ lofeuc. $)
    lofeucr $p |- ps `= ch $=
      wps wph wch wph wps lofeucr.1 lofsym lofeucr.2 loftrans $.
      $( [2-Sep-2015] $)
  $}

  ${
    lofsubr.1 $e |- ph `= ps $.
    $( A commuted version of lofsub. $)
    lofsubr $p |- et ph `= et ps $=
      wps wet lofdf-juxt wet wph lofdf-juxt wet wps lofdf-juxt wph wet
      lofdf-juxt wps wet lofdf-juxt wet wph lofdf-juxt wph wps wet lofsubr.1
      lofsub wph wet lofcmm lofeucr wps wet lofcmm lofeucr $.
      $( [2-Sep-2015] $)
  $}

  $( More versions of the substitution principle. Our lack of access to the
     implicit commutativity of 2D forces us to spell out each case. $)
  ${
    lofsubst.1 $e |- ph `= ps $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    lofsubst $p |- et ph ze `= et ps ze $=
      wph wze lofdf-juxt wps wze lofdf-juxt wet wph wps wze lofsubst.1 lofsub
      lofsubr $.
      
    $( [2-Sep-2015] $)
    lofsubstr $p |- et ph ze `= ze ps et $=
      wet wph lofdf-juxt wze lofdf-juxt wet wze lofdf-juxt wps lofdf-juxt wze
      wps lofdf-juxt wet lofdf-juxt wph wze lofdf-juxt wze wps lofdf-juxt wet
      wph wze lofdf-juxt wps wze lofdf-juxt wze wps lofdf-juxt wph wps wze
      lofsubst.1 lofsub wps wze lofcmm loftrans lofsubr wet wze wps lofdf-juxt
      lofcmm loftrans $.
      
    $( [2-Sep-2015] $)
    lofsubb1 $p |- si `[ et ph ze `] rh `= si `[ et ps ze `] rh $=
      wet wph lofdf-juxt wze lofdf-juxt lofdf-encl wet wps lofdf-juxt wze
      lofdf-juxt lofdf-encl wsi wrh wet wph lofdf-juxt wze lofdf-juxt wet wps
      lofdf-juxt wze lofdf-juxt wph wps wet wze lofsubst.1 lofsubst lofbeq
      lofsubst $.
      
    $( [2-Sep-2015] $)
    lofsubb2 $p |- si `[ et ph ze `] rh `= si `[ ze ps et `] rh $=
      wet wph lofdf-juxt wze lofdf-juxt lofdf-encl wze wps lofdf-juxt wet
      lofdf-juxt lofdf-encl wsi wrh wet wph lofdf-juxt wze lofdf-juxt wze wps
      lofdf-juxt wet lofdf-juxt wph wps wet wze lofsubst.1 lofsubstr lofbeq
      lofsubst $.
      $( [2-Sep-2015] $)
  $}

  ${
    lofrep.1 $e |- ph `= ps $.
    lofrep.2 $e |- et ph ze `= mu $.
    $( Direct substitution into an equation. $)
    lofrep $p |- et ps ze `= mu $=
      wet wph lofdf-juxt wze lofdf-juxt wet wps lofdf-juxt wze lofdf-juxt wmu
      wph wps wet wze lofrep.1 lofsubst lofrep.2 lofeucr $.
      $( [18-Sep-2015] $)
  $}

  ${
    lofreps.1 $e |- ph `= ps $.
    lofreps.2 $e |- mu `= et ph ze $.
    $( Direct substitution into a switched equation. $)
    lofreps $p |- mu `= et ps ze $=

    wet wps lofdf-juxt wze lofdf-juxt   wmu
    wph wps wet wze wmu
    lofreps.1
    wmu wet wph lofdf-juxt wze lofdf-juxt
    lofreps.2 lofsym
    lofrep
    lofsym
    $.
  $}

  ${
    lofrepbx.1 $e |- ph `= ps $.
    lofrepbx.2 $e |- si `[ et ph ze `] rh `= mu $.
    $( Direct substitution into a bounded-form equation. $)
    lofrepbx $p |- si `[ et ps ze `] rh `= mu $=
      wsi wet wph lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt wrh
      lofdf-juxt wsi wet wps lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt
      wrh lofdf-juxt wmu wph wps wet wze wsi wrh lofrepbx.1 lofsubb1 lofrepbx.2
      lofeucr $.
      $( [18-Sep-2015] $)
  $}

  ${
    lofrepbxs.1 $e |- ph `= ps $.
    lofrepbxs.2 $e |- mu `= si `[ et ph ze `] rh $.
    $( Direct substitution into a switched bounded-form equation. $)
    lofrepbxs $p |- mu `= si `[ et ps ze `] rh $=
    wsi wet wps lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt wrh lofdf-juxt
    wmu
    wph wps
    wet wze wsi wrh wmu
    
    lofrepbxs.1
    wmu  wsi wet wph lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt wrh lofdf-juxt
    lofrepbxs.2 lofsym
    lofrepbx
    lofsym
    $.
  $}

  
  ${
    lofrepbd.1  $e |- ph `= ps $.
    lofrepbd.2  $e |- `[ `[ et ph ze `] `] `= mu $.
    $( Direct substitution into a double bounded-form equation. $)
    lofrepbd    $p |- `[ `[ et ps ze `] `] `= mu $=
      ( lofdf-juxt lofdf-encl lofdf-void lofsubb1 lofbeq lofeucr ) CAHDHIZICBHD
      HIZIENOABCDJJFKLGM $.
      $( [3-Oct-2015] $)
  $}
  

  ${
    lofquad.1 $e |- ph `= ps $.
    lofquad.2 $e |- ch `= th $.
    $( Double substitution of equivalent forms. $)
    lofquad $p |- ph ch `= ps th $=
      wph wch lofdf-juxt wps wch lofdf-juxt wps wth lofdf-juxt wph wps
      lofdf-void wch lofquad.1 lofsubst wch wth wps lofdf-void lofquad.2
      lofsubst loftrans $.
      $( [2-Sep-2015] $)
  $}

  ${
    lofins.1 $e |- ph ps `= ch th $.
    $( Insert the same form into two equivalent forms. $)
    lofins $p |- ph ze ps `= ch ze th $=
      wph wze lofdf-juxt wps lofdf-juxt wze wch lofdf-juxt wth lofdf-juxt wch
      wze lofdf-juxt wth lofdf-juxt wph wze lofdf-juxt wps lofdf-juxt wze wph
      lofdf-juxt wps lofdf-juxt wze wch lofdf-juxt wth lofdf-juxt wph wze
      lofdf-juxt wze wph lofdf-juxt wps wph wze lofcmm lofsub wph wps
      lofdf-juxt wch wth lofdf-juxt wze lofins.1 lofsubr loftrans wze wch
      lofdf-juxt wch wze lofdf-juxt wth wze wch lofcmm lofsub loftrans $.
      $( [3-Sep-2015] $)
  $}

  $( Extended commutativity. $)
  lofcmmx $p  |- et ph ze ps si `= et ps ze ph si $=
    wph wze lofdf-juxt wps lofdf-juxt wps wze lofdf-juxt wph lofdf-juxt wet wsi
    wph wps wps wph wze wph wps lofcmm lofins lofsubst $.
    $( [3-Sep-2015] $)

  $( Bounded and extended commutativity. $)
  lofcmmbx $p |- rh `[ et ph ze ps si `] mu `= rh `[ et ps ze ph si `] mu $=
    wph wze lofdf-juxt wps lofdf-juxt wps wze lofdf-juxt wph lofdf-juxt wet wsi
    wrh wmu wze wze wph wps wze lofid lofsubstr lofsubb1 $.
    $( [2-Sep-2015] $)

  ${
    lofquadbx.1 $e |- ph `= ps $.
    lofquadbx.2 $e |- ch `= th $.
    $( Double substitution into a bounded and extended form. $)
    lofquadbx $p |- rh `[ et ph ze ch si `] mu `= rh `[ et ps ze th si `] mu $=
      wph wze lofdf-juxt wch lofdf-juxt wps wze lofdf-juxt wth lofdf-juxt wet
      wsi wrh wmu wph wch wps wth wze wph wps wch wth lofquadbx.1 lofquadbx.2
      lofquad lofins lofsubb1 $.
      $( [3-Sep-2015] $)
  $}

  $( It's hard to know where to stop with auxiliary theorems. Had we choosen

     to prove the two additional statements:

     tranxb.1  $e |- ph `= ps $.
     tranxb.2  $e |- ch `= ps $.
     tranxb    $p |- rh ( ze ph et ) si `= si ( et ch ze ) rh $.

     tranrxb.1  $e |- ph `= ps $.
     tranrxb.2  $e |- ph `= ch $.
     tranrxb    $p |- rh ( ze ps et ) si `= si ( et ch ze ) rh $.

     we could have reduced significantly the proof of theorem c9.0. $)


  $( Position. $)
  j1.0 $a |- `[ `[ ph `] ph `] `= $.

  $( Transposition. $)
  j2.0 $a |- `[ `[ ph ch `] `[ ps ch `] `] `= `[ `[ ph `] `[ ps `] `] ch $.

  $( System_0 consequences ------------------------------------ $)

  $( Reflexion. $)
  c1.0 $p |- `[ `[ ph `] `] `= ph $=
    wph lofdf-encl lofdf-encl wph lofdf-encl lofdf-encl wph lofdf-juxt
    lofdf-encl wph lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    wph wph lofdf-encl lofdf-encl wph wph lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl lofdf-encl wph lofdf-encl lofdf-encl wph lofdf-juxt lofdf-encl
    wph lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-encl lofdf-encl wph lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt
    lofdf-encl wph wph lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl wph wph lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-encl
    wph lofdf-encl lofdf-encl wph lofdf-encl wph lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl wph wph lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt
    lofdf-encl wph wph lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl wph lofdf-encl lofdf-encl wph lofdf-encl lofdf-encl wph
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl lofdf-juxt wph
    lofdf-encl wph lofdf-encl lofdf-encl lofdf-juxt lofdf-encl wph wph
    lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl
    lofdf-encl lofdf-juxt wph lofdf-encl lofdf-encl wph lofdf-encl lofdf-encl
    wph lofdf-encl lofdf-juxt lofdf-encl lofdf-void wph lofdf-encl lofdf-encl
    wph lofdf-encl j1.0 lofsub lofsym wph lofdf-encl wph wph lofdf-encl
    lofdf-encl j2.0 lofeuc wph lofdf-encl wph lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl wph lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl
    lofdf-void wph wph lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-void
    lofdf-void wph lofdf-encl wph lofdf-encl lofdf-encl lofdf-void lofdf-void
    lofdf-void lofdf-void lofdf-void lofcmmbx lofsubb1 loftrans wph lofdf-encl
    lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl lofdf-void lofdf-void wph
    wph lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-void lofdf-void wph
    lofdf-encl j1.0 lofsubb1 loftrans wph wph lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl wph lofdf-encl lofdf-encl wph lofdf-juxt lofdf-encl lofdf-void
    wph lofdf-encl wph lofdf-juxt lofdf-encl lofdf-void lofdf-void lofdf-void
    lofdf-void lofdf-void wph wph lofdf-encl lofdf-encl lofdf-void lofdf-void
    lofdf-void lofdf-void lofdf-void lofcmmbx wph lofdf-encl wph lofdf-juxt
    lofdf-encl lofdf-void wph j1.0 lofsym lofquadbx loftrans wph lofdf-encl
    lofdf-encl wph lofdf-juxt lofdf-encl wph lofdf-encl wph lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl lofdf-encl wph
    lofdf-encl lofdf-encl lofdf-juxt lofdf-encl wph lofdf-juxt wph wph
    lofdf-encl lofdf-encl wph lofdf-encl wph j2.0 wph lofdf-encl lofdf-encl
    lofdf-encl wph lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-void wph
    wph lofdf-encl lofdf-encl j1.0 lofsub loftrans loftrans $.
    $( [6-Sep-2015] $)

  $( Generation. $)
  c2.0 $p |- `[ ph ps `] ps `= `[ ph `] ps $=
    wph lofdf-encl wps lofdf-juxt lofdf-encl wps lofdf-encl wps lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl wph wps lofdf-juxt lofdf-encl wps
    lofdf-juxt wph lofdf-encl wps lofdf-juxt wph lofdf-encl wps lofdf-juxt
    lofdf-encl wps lofdf-encl wps lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-encl lofdf-encl wps lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    wps lofdf-juxt wph wps lofdf-juxt lofdf-encl wps lofdf-juxt wph lofdf-encl
    wps lofdf-encl wps j2.0 wph lofdf-encl lofdf-encl wph wps lofdf-encl
    lofdf-encl wps lofdf-void lofdf-void lofdf-void lofdf-void wps wph c1.0 wps
    c1.0 lofquadbx loftrans wph lofdf-encl wps lofdf-juxt lofdf-encl wps
    lofdf-encl wps lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl
    wps lofdf-juxt lofdf-encl lofdf-encl wph lofdf-encl wps lofdf-juxt wps
    lofdf-encl wps lofdf-juxt lofdf-encl lofdf-void wph lofdf-encl wps
    lofdf-juxt lofdf-encl lofdf-void lofdf-void lofdf-void wps j1.0 lofsubb1
    wph lofdf-encl wps lofdf-juxt c1.0 loftrans lofeucr $.
    $( [6-Sep-2015] $)

  $( Integration. $)
  c3.0 $p |- `[ `] ph `= `[ `] $=
    wph lofdf-encl wph lofdf-juxt lofdf-void lofdf-encl wph lofdf-juxt
    lofdf-void lofdf-encl lofdf-void wph c2.0 wph lofdf-encl wph lofdf-juxt
    lofdf-encl lofdf-encl wph lofdf-encl wph lofdf-juxt lofdf-void lofdf-encl
    wph lofdf-encl wph lofdf-juxt c1.0 wph lofdf-encl wph lofdf-juxt lofdf-encl
    lofdf-void wph j1.0 lofbeq lofeucr lofeucr $.
    $( [6-Sep-2015] $)

  $( Iteration. $)
  c5.0 $p |- ph ph `= ph $=
    wph lofdf-encl wph lofdf-juxt lofdf-encl wph lofdf-juxt wph wph lofdf-juxt
    wph wph lofdf-encl wph lofdf-juxt lofdf-encl wph lofdf-juxt wph lofdf-encl
    lofdf-encl wph lofdf-juxt wph wph lofdf-juxt wph lofdf-encl wph c2.0 wph
    lofdf-encl lofdf-encl wph lofdf-void wph wph c1.0 lofsubst loftrans wph
    lofdf-encl wph lofdf-juxt lofdf-encl lofdf-void lofdf-void wph wph j1.0
    lofsubst lofeucr $.
    $( [6-Sep-2015] $)

  $( Occultation. $)
  c4.0 $p |- `[ `[ ph `] ps `] ph `= ph $=
    wph lofdf-encl wps lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-void
    lofdf-encl lofdf-encl wph lofdf-juxt wph wph lofdf-encl wps lofdf-juxt
    lofdf-encl wph lofdf-juxt lofdf-void lofdf-encl wps lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-void lofdf-encl lofdf-encl wph
    lofdf-juxt wph lofdf-encl wps lofdf-juxt lofdf-encl wph lofdf-juxt wph
    lofdf-encl wps lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    lofdf-void lofdf-encl wps lofdf-encl lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-juxt wph wph lofdf-juxt lofdf-encl wps lofdf-encl wph lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl
    wph lofdf-juxt wph lofdf-encl wps lofdf-encl wph lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl wph wph lofdf-juxt lofdf-encl wps lofdf-encl wph
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-encl
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-juxt wph lofdf-encl wps
    lofdf-juxt lofdf-encl wph lofdf-juxt wph wps lofdf-encl wph j2.0 wps
    lofdf-encl lofdf-encl wps wph lofdf-encl lofdf-void lofdf-void wph wps c1.0
    lofsubb1 loftrans wph wph lofdf-juxt lofdf-encl wph lofdf-encl lofdf-void
    wps lofdf-encl wph lofdf-juxt lofdf-encl lofdf-void lofdf-void wph wph
    lofdf-juxt wph lofdf-void lofdf-void lofdf-void lofdf-void wph c5.0
    lofsubb1 lofsubb1 lofeucr lofdf-void wps lofdf-encl wph j2.0 loftrans
    lofdf-void lofdf-encl wps lofdf-encl lofdf-encl lofdf-juxt lofdf-void
    lofdf-encl lofdf-void lofdf-void lofdf-void wph wps lofdf-encl lofdf-encl
    c3.0 lofsubb1 loftrans lofdf-void lofdf-encl lofdf-encl lofdf-void
    lofdf-void wph lofdf-void c1.0 lofsubst loftrans $.
    $( [6-Sep-2015] $)

  $( Extension. $)
  c6.0 $p |- `[ `[ ph `] `[ ps `] `] `[ `[ ph `] ps `] `= ph $=
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl lofdf-encl wph wph
    lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-encl wph lofdf-encl wps
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl
    lofdf-juxt wph lofdf-encl lofdf-encl wph lofdf-encl wps lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl lofdf-juxt
    c1.0 wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-encl wps lofdf-encl
    lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl lofdf-juxt
    lofdf-encl wph lofdf-encl lofdf-encl wph lofdf-encl wps lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl wps lofdf-encl lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-juxt
    lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    wps lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl wps wph lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl lofdf-encl wps
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl lofdf-juxt wph lofdf-encl
    wps lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wph lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl wps wph
    lofdf-encl lofdf-juxt lofdf-encl lofdf-void lofdf-void lofdf-void
    lofdf-void lofdf-void wph lofdf-encl wps lofdf-encl lofdf-void lofdf-void
    lofdf-void lofdf-void lofdf-void lofcmmbx wph lofdf-encl wps lofdf-void
    lofdf-void lofdf-void lofdf-void lofdf-void lofcmmbx lofquadbx wps
    lofdf-encl wps wph lofdf-encl j2.0 loftrans lofbeq wps lofdf-encl
    lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-void lofdf-void wph
    lofdf-encl lofdf-void lofdf-void wps lofdf-encl j1.0 lofsubb1 loftrans
    lofeucr wph c1.0 loftrans $.
    $( [6-Sep-2015] $)

  $( Echelon. $)
  c7.0 $p |- `[ `[ `[ ph `] ps `] ch `] `= `[ ph ch `] `[ `[ ps `] ch `] $=
    wph wch lofdf-juxt lofdf-encl wps lofdf-encl wch lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl
    wch lofdf-juxt lofdf-encl wph wch lofdf-juxt lofdf-encl wps lofdf-encl wch
    lofdf-juxt lofdf-encl lofdf-juxt wph wch lofdf-juxt lofdf-encl wps
    lofdf-encl wch lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-encl wph
    lofdf-encl wps lofdf-encl lofdf-encl lofdf-juxt lofdf-encl wch lofdf-juxt
    lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt
    lofdf-encl wph wch lofdf-juxt lofdf-encl wps lofdf-encl wch lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl wch lofdf-juxt wph wps lofdf-encl wch j2.0 lofbeq wph
    lofdf-encl wps lofdf-encl lofdf-encl lofdf-juxt lofdf-encl wch lofdf-juxt
    wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt wps lofdf-encl
    lofdf-encl wps wph lofdf-encl lofdf-void lofdf-void wch wps c1.0 lofsubb1
    lofbeq loftrans wph wch lofdf-juxt lofdf-encl wps lofdf-encl wch lofdf-juxt
    lofdf-encl lofdf-juxt c1.0 lofeucr $.
    $( [6-Sep-2015] $)

  $( Modified transposition. $)
  c8.0 $p |- `[ `[ ph `] `[ ps th `] `[ ch th `] `] 
             `= `[ `[ ph `] `[ ps `] `[ ch `] `] `[ `[ ph `] `[ th `] `] $=
    wph lofdf-encl wps wth lofdf-juxt lofdf-encl lofdf-juxt wch wth lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wch lofdf-encl lofdf-juxt
    lofdf-encl wth lofdf-juxt lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-encl wps lofdf-encl lofdf-juxt wch lofdf-encl lofdf-juxt
    lofdf-encl wph lofdf-encl wth lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    wps wth lofdf-juxt lofdf-encl wch wth lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lofdf-encl wps wth lofdf-juxt lofdf-encl wch wth lofdf-juxt
    lofdf-encl lofdf-juxt wph lofdf-encl lofdf-void lofdf-void lofdf-void wps
    lofdf-encl wch lofdf-encl lofdf-juxt lofdf-encl wth lofdf-juxt lofdf-encl
    wph lofdf-encl lofdf-juxt lofdf-encl wps wth lofdf-juxt lofdf-encl wch wth
    lofdf-juxt lofdf-encl lofdf-juxt c1.0 wps wth lofdf-juxt lofdf-encl wch wth
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-encl wps lofdf-encl wch
    lofdf-encl lofdf-juxt lofdf-encl wth lofdf-juxt lofdf-encl wph lofdf-encl
    lofdf-void lofdf-void lofdf-void wps wth lofdf-juxt lofdf-encl wch wth
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wch lofdf-encl
    lofdf-juxt lofdf-encl wth lofdf-juxt wps wch wth j2.0 lofbeq lofsubb2
    lofrepbx wps lofdf-encl wch lofdf-encl lofdf-juxt lofdf-encl wth lofdf-juxt
    lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wch
    lofdf-encl lofdf-juxt wph lofdf-encl lofdf-juxt lofdf-encl wth lofdf-encl
    wph lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps
    lofdf-encl lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl
    wth lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wch
    lofdf-encl lofdf-juxt wth wph lofdf-encl c7.0 wps lofdf-encl wch lofdf-encl
    lofdf-juxt wph lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-encl lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl wth lofdf-encl
    wph lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wth lofdf-encl
    lofdf-juxt lofdf-encl wps lofdf-encl wch lofdf-encl lofdf-juxt wph
    lofdf-encl lofdf-void lofdf-void lofdf-void lofdf-void lofdf-void lofcmmbx
    wth lofdf-encl wph lofdf-encl lofdf-void lofdf-void lofdf-void lofdf-void
    lofdf-void lofcmmbx lofquad loftrans loftrans $.
    $( [6-Sep-2015] $)

  $( Crosstransposition. $)
  c9.0 $p |- `[ `[ `[ ps `] `[ ph `] `] `[ `[ ch `] `[ ph `] `]
             `[ `[ th `] ph `] `[ `[ ta `] ph `] `]
             `= `[ `[ ph `] ps ch `] `[ ph th ta `] $=
    wps lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl wch lofdf-encl wph
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wth lofdf-encl wph lofdf-juxt
    lofdf-encl lofdf-juxt wta lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl wth wta lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl wps
    lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wch lofdf-encl
    wph lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl
    wps lofdf-juxt wch lofdf-juxt lofdf-encl wph wth lofdf-juxt wta lofdf-juxt
    lofdf-encl lofdf-juxt wth lofdf-encl wph lofdf-juxt lofdf-encl wta
    lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt wth wta lofdf-juxt
    lofdf-encl wph lofdf-juxt lofdf-encl wps lofdf-encl wph lofdf-encl
    lofdf-juxt lofdf-encl wch lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-void lofdf-void lofdf-void wth lofdf-encl wph lofdf-juxt
    lofdf-encl wta lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    lofdf-encl wth lofdf-encl wph lofdf-juxt lofdf-encl wta lofdf-encl wph
    lofdf-juxt lofdf-encl lofdf-juxt wth wta lofdf-juxt lofdf-encl wph
    lofdf-juxt lofdf-encl wth lofdf-encl wph lofdf-juxt lofdf-encl wta
    lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt c1.0 wth lofdf-encl wph
    lofdf-juxt lofdf-encl wta lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl wth wta lofdf-juxt lofdf-encl wph lofdf-juxt wth lofdf-encl wph
    lofdf-juxt lofdf-encl wta lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl wth lofdf-encl lofdf-encl wta lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl wph lofdf-juxt wth wta lofdf-juxt lofdf-encl wph lofdf-juxt wth
    lofdf-encl wta lofdf-encl wph j2.0 wth lofdf-encl lofdf-encl wth wta
    lofdf-encl lofdf-encl wta lofdf-void lofdf-void lofdf-void lofdf-void wph
    wth c1.0 wta c1.0 lofquadbx loftrans lofbeq lofeucr lofsubb2 wth wta
    lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl wps lofdf-encl wph
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wch lofdf-encl wph lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wth wta lofdf-juxt lofdf-encl
    wph lofdf-juxt lofdf-encl wps lofdf-juxt wch lofdf-juxt lofdf-encl wth wta
    lofdf-juxt wph lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps
    lofdf-juxt wch lofdf-juxt lofdf-encl wph wth lofdf-juxt wta lofdf-juxt
    lofdf-encl lofdf-juxt wth wta lofdf-juxt lofdf-encl wph lofdf-juxt
    lofdf-encl wps lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    wch lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    wth wta lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl wps lofdf-juxt wch
    lofdf-juxt lofdf-encl wth wta lofdf-juxt lofdf-encl lofdf-encl wph
    lofdf-juxt lofdf-encl lofdf-juxt wth wta lofdf-juxt lofdf-encl wph
    lofdf-juxt lofdf-encl wps lofdf-juxt wch lofdf-juxt lofdf-encl wth wta
    lofdf-juxt wph lofdf-juxt lofdf-encl lofdf-juxt wth wta lofdf-juxt
    lofdf-encl wph lofdf-juxt lofdf-encl wps lofdf-encl wph lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt wch lofdf-encl wph lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl wth wta lofdf-juxt lofdf-encl wph
    lofdf-juxt lofdf-encl wps lofdf-juxt wch lofdf-juxt lofdf-encl wth wta
    lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl
    lofdf-juxt wth wta lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl wps
    lofdf-juxt wch lofdf-juxt lofdf-encl wth wta lofdf-juxt lofdf-encl
    lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt wth wta lofdf-juxt
    lofdf-encl wph lofdf-juxt lofdf-encl wps lofdf-encl wph lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt wch lofdf-encl wph lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl wth wta lofdf-juxt lofdf-encl wph
    lofdf-juxt lofdf-encl wps lofdf-juxt wch lofdf-juxt lofdf-encl wth wta
    lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt wth wta lofdf-juxt lofdf-encl wph
    lofdf-juxt lofdf-encl wps lofdf-juxt wch lofdf-juxt lofdf-encl wth wta
    lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl
    lofdf-juxt wth wta lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl wps
    lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wch lofdf-encl
    wph lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wth wta
    lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl wps lofdf-encl lofdf-encl
    lofdf-juxt wch lofdf-encl lofdf-encl lofdf-juxt lofdf-encl wth wta
    lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt wth wta lofdf-juxt lofdf-encl wph
    lofdf-juxt lofdf-encl wps lofdf-juxt wch lofdf-juxt lofdf-encl wth wta
    lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt wth wta lofdf-juxt lofdf-encl wph
    lofdf-juxt wps lofdf-encl wch lofdf-encl wph lofdf-encl c8.0 wps lofdf-encl
    lofdf-encl wps wch lofdf-encl lofdf-encl wch wth wta lofdf-juxt lofdf-encl
    wph lofdf-juxt lofdf-encl lofdf-void lofdf-void lofdf-void wth wta
    lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl wps c1.0 wch c1.0 lofquadbx loftrans wph lofdf-encl
    lofdf-encl wph wth wta lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl
    lofdf-void wth wta lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl wps
    lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-void wph c1.0 lofsubb1 loftrans
    wth wta lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl wph lofdf-juxt wth
    wta lofdf-juxt lofdf-encl lofdf-encl wph lofdf-juxt lofdf-void lofdf-void
    wth wta lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl wps lofdf-juxt wch
    lofdf-juxt lofdf-encl lofdf-void wth wta lofdf-juxt lofdf-encl wph c2.0
    lofsubb1 loftrans wth wta lofdf-juxt lofdf-encl lofdf-encl wth wta
    lofdf-juxt lofdf-void wph wth wta lofdf-juxt lofdf-encl wph lofdf-juxt
    lofdf-encl wps lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-void wth wta
    lofdf-juxt c1.0 lofsubb1 loftrans wth wta lofdf-juxt lofdf-encl wph
    lofdf-juxt lofdf-encl wps lofdf-juxt wch lofdf-juxt wth wta lofdf-juxt wph
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wth wta lofdf-juxt wph
    lofdf-juxt lofdf-encl lofdf-juxt wth wta lofdf-juxt lofdf-encl wph
    lofdf-juxt lofdf-encl wps lofdf-juxt wch lofdf-juxt lofdf-encl wth wta
    lofdf-juxt wph lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps
    lofdf-juxt wch lofdf-juxt lofdf-encl wph wth lofdf-juxt wta lofdf-juxt
    lofdf-encl lofdf-juxt wth wta lofdf-juxt lofdf-encl wph lofdf-juxt
    lofdf-encl wps lofdf-juxt wch lofdf-juxt wth wta lofdf-juxt wph lofdf-juxt
    lofdf-encl c2.0 wth wta lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl wps
    lofdf-juxt wch lofdf-juxt wth wta lofdf-juxt wph lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl wth wta lofdf-juxt wph lofdf-juxt lofdf-encl
    lofdf-juxt wph wth wta lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wps
    lofdf-juxt wch lofdf-juxt wph wth lofdf-juxt wta lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl wth wta lofdf-juxt wph lofdf-juxt lofdf-encl
    lofdf-juxt wph lofdf-encl wps lofdf-juxt wch lofdf-juxt lofdf-encl wph wth
    lofdf-juxt wta lofdf-juxt lofdf-encl lofdf-juxt wth wta lofdf-juxt
    lofdf-encl wph lofdf-juxt lofdf-encl wph wth wta lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl wth wta lofdf-juxt wph lofdf-juxt lofdf-encl wph wth
    lofdf-juxt wta lofdf-juxt lofdf-encl lofdf-void wps wch lofdf-juxt
    lofdf-void lofdf-void wth wta lofdf-juxt wph lofdf-juxt lofdf-encl wth wta
    lofdf-juxt lofdf-encl wph lofdf-void lofdf-void lofdf-void lofdf-void
    lofdf-void lofcmmbx wth wta lofdf-juxt wph lofdf-void lofdf-void lofdf-void
    lofdf-void lofdf-void lofcmmbx lofquadbx wph lofdf-encl lofdf-encl wth wta
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wps lofdf-juxt wch lofdf-juxt
    wph lofdf-encl lofdf-encl wth lofdf-juxt wta lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl wth wta lofdf-juxt wph lofdf-juxt lofdf-encl
    lofdf-juxt wph wth wta lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wps
    lofdf-juxt wch lofdf-juxt wph wth lofdf-juxt wta lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl wth wta lofdf-juxt wph lofdf-juxt lofdf-encl
    lofdf-juxt wph lofdf-encl wps lofdf-juxt wch lofdf-juxt lofdf-encl wph wth
    lofdf-juxt wta lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl lofdf-encl
    wth wta lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wps lofdf-juxt wch
    lofdf-juxt wph wth wta lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wps
    lofdf-juxt wch lofdf-juxt wph lofdf-encl lofdf-encl wth lofdf-juxt wta
    lofdf-juxt lofdf-encl wph wth lofdf-juxt wta lofdf-juxt lofdf-encl
    lofdf-void lofdf-void lofdf-void lofdf-void wth wta lofdf-juxt wph
    lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl wph lofdf-void wth wta
    lofdf-juxt lofdf-encl lofdf-void wps wch lofdf-juxt wph c1.0 lofsubb1 wph
    lofdf-encl lofdf-encl wph lofdf-void wth wta lofdf-juxt lofdf-void
    lofdf-void wph c1.0 lofsubb1 lofquadbx wph lofdf-encl lofdf-encl wth wta
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wps lofdf-juxt wch lofdf-juxt
    wph lofdf-encl lofdf-encl wth lofdf-juxt wta lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl wth wta lofdf-juxt wph lofdf-juxt lofdf-encl
    lofdf-juxt wph lofdf-encl lofdf-encl wth wta lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl wth lofdf-juxt wta
    lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-juxt wch lofdf-juxt lofdf-encl
    wth wta lofdf-juxt wph lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps
    lofdf-juxt wch lofdf-juxt lofdf-encl wph wth lofdf-juxt wta lofdf-juxt
    lofdf-encl lofdf-juxt wps wch lofdf-juxt wph lofdf-encl lofdf-encl wth
    lofdf-juxt wta lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl wth wta
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-void lofdf-void
    lofdf-void wth wta lofdf-juxt wph lofdf-juxt lofdf-encl lofcmmbx wph
    lofdf-encl lofdf-encl wth wta lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-encl lofdf-encl wth lofdf-juxt wta lofdf-juxt lofdf-encl
    lofdf-juxt wps lofdf-juxt wch lofdf-juxt lofdf-encl wth wta lofdf-juxt wph
    lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-juxt wch
    lofdf-juxt lofdf-encl wth wta lofdf-juxt wph lofdf-juxt lofdf-encl
    lofdf-juxt wph lofdf-encl wps lofdf-juxt wch lofdf-juxt lofdf-encl wph wth
    lofdf-juxt wta lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl lofdf-encl
    wth wta lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl
    lofdf-encl wth lofdf-juxt wta lofdf-juxt lofdf-encl lofdf-juxt wph
    lofdf-encl lofdf-void wps wch lofdf-juxt lofdf-void wth wta lofdf-juxt wph
    lofdf-juxt lofdf-encl wph lofdf-encl wth wta lofdf-juxt c6.0 lofsubb1 wth
    wta lofdf-juxt wph lofdf-void lofdf-void lofdf-void wph lofdf-encl wps
    lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-void lofcmmbx loftrans loftrans
    lofeucr loftrans lofeucr loftrans loftrans $.
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
  c5.1 $a |- ph ph `= ph $.
  $( PLEASE PUT DESCRIPTION HERE. $)
  c6.1 $a |- `[ `[ ph `] `[ ps `] `] `[ `[ ph `] ps `] `= ph $.

  $( System_1 consequences ------------------------------------ $)

  $( Lemma for proof of c1.1.  Under the dual interpretation, this is mildly
     reminiscent of modus ponens:  (p & (p -> q)) ` = (p & q). $)
  lem1.1 $p |- ph `[ `[ ps `] ph `] `= ph ps $=
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wph lofdf-encl lofdf-juxt
    lofdf-encl wps lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt lofdf-juxt
    wph wps lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt wph wps lofdf-juxt
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wph lofdf-encl lofdf-juxt
    lofdf-encl wps lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt lofdf-juxt
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wph lofdf-juxt lofdf-encl
    lofdf-juxt wph wps lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt wph
    lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wph lofdf-encl lofdf-juxt
    lofdf-encl wps lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt lofdf-juxt
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-juxt
    lofdf-encl wps lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt lofdf-juxt
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wph lofdf-juxt lofdf-encl
    lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-encl wps lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wph
    lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wph lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-encl wps lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps
    lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wph lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph
    lofdf-encl wps lofdf-juxt lofdf-encl wps lofdf-encl wph lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-juxt wps lofdf-encl wph lofdf-encl lofdf-juxt
    lofdf-encl wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wph lofdf-juxt lofdf-encl
    wps lofdf-encl wph lofdf-encl lofdf-void lofdf-void lofdf-void lofdf-void
    lofdf-void lofcmmbx lofsubst wph lofdf-encl wps lofdf-juxt lofdf-encl wph
    lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-encl lofdf-juxt lofdf-encl lofdf-void wps lofdf-encl wph lofdf-juxt
    lofdf-encl lofcmmx loftrans wph lofdf-encl wps lofdf-encl lofdf-juxt
    lofdf-encl wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-juxt lofdf-encl wps lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl c5.1 lofsub loftrans
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-juxt lofdf-encl lofdf-juxt wph wps lofdf-encl wph lofdf-juxt
    lofdf-encl wph wps c6.1 lofsub loftrans wph lofdf-encl wps lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl lofdf-juxt
    wph wps lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wph
    lofdf-juxt lofdf-encl lofdf-juxt wps wph wps c6.1 wps wph c6.1 lofquad
    lofeucr $.
    
  $( [17-Sep-2015] $)
  c1.1 $p |- `[ `[ ph `] `] `= ph $=
    lofdf-void wph lem1.1 $.
    $( [17-Sep-2015] $)

  $( The LoF I2 arithmetic initial.  This is also directly derivable from the
     basis by plugging void values into c6.1, followed by two applications of
     c5.1. $)
  i2.1 $p |- `[ `[ `] `] `= $=
    lofdf-void c1.1 $.
    $( [17-Sep-2015] $)

  $( One of the two equations from Basis_0. $)
  j1.1 $p |- `[ `[ ph `] ph `] `= $=
    wph lofdf-encl wph lofdf-juxt lofdf-encl lofdf-void lofdf-encl lofdf-encl
    lofdf-void wph lofdf-encl wph lofdf-juxt lofdf-void lofdf-encl wph
    lofdf-encl wph lofdf-encl lofdf-encl lofdf-juxt wph lofdf-encl wph
    lofdf-juxt lofdf-void lofdf-encl wph lofdf-encl lofdf-encl wph wph
    lofdf-encl wph c1.1 lofsubr wph lofdf-encl lofdf-encl wph lofdf-encl
    lofdf-juxt wph lofdf-encl wph lofdf-encl lofdf-encl lofdf-juxt lofdf-void
    lofdf-encl wph lofdf-encl lofdf-encl wph lofdf-encl lofcmm lofdf-void
    lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl lofdf-void
    lofdf-encl lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl
    lofdf-encl wph lofdf-encl lofdf-juxt lofdf-void lofdf-encl lofdf-void
    lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl
    lofdf-encl lofdf-void lofdf-encl lofdf-encl wph lofdf-juxt lofdf-encl wph
    lofdf-encl lofdf-void lofdf-encl lofdf-encl lofdf-void lofdf-void wph
    lofdf-encl lofdf-void lofdf-void i2.1 lofsubb1 lofdf-void lofdf-encl
    lofdf-encl lofdf-void lofdf-void wph lofdf-void lofdf-void i2.1 lofsubb1
    lofquad lofdf-void lofdf-encl wph c6.1 lofeucr lofeucr lofeucr lofbeq i2.1
    loftrans $.
    
  $( [17-Sep-2015] $)
  c4.1 $p |- `[ `[ ph `] ps `] ph `= ph $=
    wph lofdf-encl wps lofdf-juxt lofdf-encl wph lofdf-juxt wph lofdf-encl wps
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl
    lofdf-juxt wph wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-encl wps lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps
    lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-juxt lofdf-encl
    wph lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-encl wps lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl
    lofdf-juxt wph lofdf-void wph lofdf-encl wps lofdf-juxt lofdf-encl wph wps
    c6.1 lofsubstr wph lofdf-encl wps lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-juxt lofdf-encl
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-juxt lofdf-encl c5.1 lofsubr lofeucr wph wps c6.1 loftrans $.
    $( [18-Sep-2015] $)

  $( Corollary of c4.1 $)
  c4cor.1 $p |- `[ ph ps `] `[ ph `] `= `[ ph `] $=
    wph lofdf-encl lofdf-encl wps lofdf-juxt lofdf-encl wph lofdf-encl
    lofdf-juxt wph wps lofdf-juxt lofdf-encl wph lofdf-encl lofdf-juxt wph
    lofdf-encl wph lofdf-encl lofdf-encl wph lofdf-void wps lofdf-void wph
    lofdf-encl wph c1.1 lofsubb1 wph lofdf-encl wps c4.1 lofeucr $.
    $( [18-Sep-2015] $)

  $( Corollary of c6.1 $)
  c6cor.1 $p |- `[ `[ ph `] ps `] `[ ph ps `] `= `[ ps `] $=
    wps wph lofdf-juxt wph wps lofdf-juxt lofdf-void lofdf-void wph lofdf-encl
    wps lofdf-juxt lofdf-encl lofdf-void wps lofdf-encl wps wph lofcmm wps wph
    lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-juxt lofdf-void lofdf-void
    lofdf-void wps wph lofdf-juxt lofdf-encl wps lofdf-encl wps wph lofdf-encl
    lofcmm wps lofdf-encl lofdf-encl wps lofdf-void wph wps wph lofdf-encl
    lofdf-juxt lofdf-encl lofdf-void wps lofdf-encl wps c1.1 wps lofdf-encl
    lofdf-encl wps lofdf-void wph lofdf-encl lofdf-void wps lofdf-encl
    lofdf-encl wph lofdf-juxt lofdf-encl wps lofdf-encl wps c1.1 wps lofdf-encl
    wph c6.1 lofrepbx lofrepbx lofrepbx lofrepbx $.
    
  $( [22-Sep-2015] $)
  c7.1 $p |- `[ `[ `[ ph `] ps `] ch `] `= `[ ph ch `] `[ `[ ps `] ch `] $=
    wph wch lofdf-juxt lofdf-encl wps lofdf-encl wch lofdf-juxt lofdf-encl
    lofdf-juxt wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt
    lofdf-encl wch wps lofdf-encl lofdf-juxt wps lofdf-encl wch lofdf-juxt
    lofdf-void lofdf-void wph wch lofdf-juxt lofdf-encl lofdf-void wph
    lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt lofdf-encl wch wps
    lofdf-encl lofcmm wch wph lofdf-juxt wph wch lofdf-juxt lofdf-void
    lofdf-void lofdf-void wch wps lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt lofdf-encl wch wph
    lofcmm wch wps lofdf-encl lofdf-juxt wph lofdf-encl lofdf-juxt lofdf-encl
    wch wps lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wch wps lofdf-encl
    lofdf-juxt lofdf-encl wch wph lofdf-juxt lofdf-encl lofdf-void wph
    lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt lofdf-encl wch wps
    lofdf-encl lofdf-juxt wph lofdf-encl c4cor.1 wph lofdf-encl wch lofdf-juxt
    wps lofdf-encl lofdf-juxt wch wps lofdf-encl lofdf-juxt wph lofdf-encl
    lofdf-juxt lofdf-void lofdf-void wch wph lofdf-juxt lofdf-encl wch wps
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl
    wch lofdf-juxt lofdf-encl wph lofdf-encl wch wps lofdf-encl lofdf-juxt
    lofcmm wch wps lofdf-encl lofdf-juxt lofdf-encl wch wph lofdf-juxt
    lofdf-encl wph lofdf-encl wch lofdf-juxt wps lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-juxt wch wph lofdf-juxt lofdf-encl wph
    lofdf-encl wch lofdf-juxt wps lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    wch wps lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-void lofdf-void
    wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt lofdf-encl wch wps
    lofdf-encl lofdf-juxt lofdf-encl wch wph lofdf-juxt lofdf-encl wph
    lofdf-encl wch lofdf-juxt wps lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lofcmm wch wph lofdf-juxt wps lofdf-juxt lofdf-encl wch wph lofdf-juxt
    lofdf-encl lofdf-juxt wch wph lofdf-juxt lofdf-encl wch wps lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-encl wch lofdf-juxt wps lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl wch
    lofdf-juxt lofdf-encl wch wph lofdf-juxt wps c4cor.1 wch wps lofdf-encl
    lofdf-juxt lofdf-encl wch wph lofdf-juxt wps lofdf-juxt lofdf-encl
    lofdf-juxt wch wph lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wch
    lofdf-juxt wps lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl
    wps lofdf-juxt lofdf-encl wch lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-juxt lofdf-encl wch lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl
    wps lofdf-juxt lofdf-encl wch lofdf-juxt lofdf-encl wch wps lofdf-encl
    lofdf-juxt lofdf-encl wch wph lofdf-juxt wps lofdf-juxt lofdf-encl
    lofdf-juxt wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt
    lofdf-encl wch wph lofdf-juxt lofdf-encl wph lofdf-encl wch lofdf-juxt wps
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-juxt
    lofdf-encl wch lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt
    lofdf-encl wph wps lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wch
    lofdf-void lofdf-void wch wph lofdf-juxt wps lofdf-juxt lofdf-encl wph
    lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt lofdf-encl wph wps
    c6cor.1 wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt wch wph
    lofdf-encl wps lofdf-juxt lofdf-encl lofdf-juxt lofdf-void wph wps
    lofdf-juxt lofdf-encl lofdf-void wch wph lofdf-juxt wps lofdf-juxt
    lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt
    lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofcmm wph
    lofdf-encl wps lofdf-juxt lofdf-encl wph lofdf-juxt wph wch wps wph
    lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt wph wps lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lofdf-void wph lofdf-encl wps lofdf-juxt
    lofdf-encl wch lofdf-juxt lofdf-encl wph wps c4.1 wph lofdf-encl wps
    lofdf-juxt lofdf-encl wch lofdf-juxt wch wph lofdf-encl wps lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-void wph wps lofdf-juxt wph lofdf-encl wps
    lofdf-juxt lofdf-encl wch lofdf-juxt wph wps lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl lofdf-void wph lofdf-encl wps lofdf-juxt lofdf-encl
    wch lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl wch
    lofcmm wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt lofdf-encl
    lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt
    lofdf-void wph wps lofdf-juxt wph lofdf-encl wps lofdf-juxt lofdf-encl wch
    lofdf-juxt wph wps lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-void
    wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt lofdf-encl wph
    lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt c1.1 wph lofdf-encl wps
    lofdf-juxt lofdf-encl wch lofdf-juxt lofdf-encl lofdf-encl wph lofdf-encl
    wps lofdf-juxt lofdf-encl wch lofdf-juxt lofdf-void wph wps lofdf-juxt
    lofdf-encl lofdf-void wph lofdf-encl wps lofdf-juxt lofdf-encl wch
    lofdf-juxt lofdf-encl lofdf-encl wph wps lofdf-juxt lofdf-juxt lofdf-encl
    wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt lofdf-encl wph
    lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt c1.1 wph lofdf-encl wps
    lofdf-juxt lofdf-encl wch lofdf-juxt lofdf-encl wph wps lofdf-juxt c6.1
    lofrepbx lofrepbx lofrepbx lofrepbx lofrepbx lofrepbx wps wph lofdf-encl
    lofdf-juxt lofdf-encl wps lofdf-encl lofdf-juxt wps lofdf-encl wph
    lofdf-encl wch lofdf-juxt lofdf-void wch wph lofdf-juxt lofdf-encl
    lofdf-void wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt
    lofdf-encl wps wph lofdf-encl c4cor.1 wph lofdf-encl wch lofdf-juxt wph
    lofdf-encl wps lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl lofdf-juxt
    wph lofdf-encl wch lofdf-juxt wps wph lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt wps lofdf-encl lofdf-juxt lofdf-void lofdf-void wch wph
    lofdf-juxt lofdf-encl lofdf-void wph lofdf-encl wps lofdf-juxt lofdf-encl
    wch lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-void lofdf-void
    lofdf-void wph lofdf-encl wch lofdf-juxt wps lofdf-encl lofcmmbx wch wph
    lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl wch
    lofdf-juxt wph lofdf-encl lofdf-juxt wps lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt wch wph lofdf-juxt lofdf-encl wph lofdf-encl wch lofdf-juxt wph
    lofdf-encl wps lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-juxt lofdf-encl wch
    lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl wph
    lofdf-encl lofdf-void wch wps lofdf-encl wch wph lofdf-juxt lofdf-encl
    lofdf-void lofcmmbx wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-encl wps lofdf-juxt lofdf-encl lofdf-juxt wph wch lofdf-void
    lofdf-void wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt wph
    lofdf-encl lofdf-juxt wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl
    wps lofdf-juxt lofdf-encl wch lofdf-juxt lofdf-encl wph wps c6.1 wph
    lofdf-encl wps lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-juxt
    lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl lofdf-juxt wch
    lofdf-void lofdf-void wph lofdf-encl wps lofdf-juxt lofdf-encl wch
    lofdf-juxt wph lofdf-encl lofdf-juxt wps lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt lofdf-encl wph
    lofdf-encl wps lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-encl
    lofdf-juxt lofdf-encl lofcmm wph lofdf-encl wps lofdf-juxt lofdf-encl wch
    lofdf-juxt wch wph lofdf-encl wps lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-void wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-void
    wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt wph lofdf-encl
    lofdf-juxt wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-juxt lofdf-encl wch lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-juxt lofdf-encl wch lofcmm wph lofdf-encl wps lofdf-juxt lofdf-encl
    wch lofdf-juxt lofdf-encl lofdf-encl wph lofdf-encl wps lofdf-juxt
    lofdf-encl wch lofdf-juxt lofdf-void wph lofdf-encl wps lofdf-encl
    lofdf-juxt wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt wph
    lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    lofdf-void wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt
    lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt c1.1 wph
    lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt lofdf-encl lofdf-encl
    wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt lofdf-void wph
    lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-void wph lofdf-encl
    wps lofdf-juxt lofdf-encl wch lofdf-juxt lofdf-encl lofdf-encl wph
    lofdf-encl wps lofdf-encl lofdf-juxt lofdf-juxt lofdf-encl wph lofdf-encl
    wps lofdf-juxt lofdf-encl wch lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-juxt lofdf-encl wch lofdf-juxt c1.1 wph lofdf-encl wps lofdf-juxt
    lofdf-encl wch lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-encl
    lofdf-juxt c6.1 lofrepbx lofrepbx lofrepbx lofrepbx lofrepbx lofeucr
    lofrepbx lofrepbx lofquad wph lofdf-encl wps lofdf-juxt lofdf-encl wch
    lofdf-juxt lofdf-encl c5.1 loftrans lofrep lofrep lofrepbx lofrep lofrepbx
    lofrepbx lofsym $.
    $( [23-Sep-2015] $)

  $( The second of the two equations from Basis_0.  This completes the proof
     that Basis_1 is at least as powerful as Basis_0. $)
  j2.1 $p |- `[ `[ ph `] `[ ps `] `] ch `= `[ `[ ph ch `] `[ ps ch `] `] $=
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wch lofdf-juxt
    lofdf-encl lofdf-encl wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl
    wch lofdf-juxt wph wch lofdf-juxt lofdf-encl wps wch lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl
    wch lofdf-juxt c1.1 wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wch
    lofdf-juxt lofdf-encl wph wch lofdf-juxt lofdf-encl wps wch lofdf-juxt
    lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl
    wch lofdf-juxt lofdf-encl wph wch lofdf-juxt lofdf-encl wps lofdf-encl
    lofdf-encl wch lofdf-juxt lofdf-encl lofdf-juxt wph wch lofdf-juxt
    lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt wph wps lofdf-encl wch
    c7.1 wps lofdf-encl lofdf-encl wps lofdf-void wch wph wch lofdf-juxt
    lofdf-encl lofdf-void wps c1.1 lofsubb1 loftrans lofbeq lofeucr $.
    $( [23-Sep-2015] $)

$( =======================================================================

     System_2

     Having shown that C5 and C6 form a basis, I now show that C6 alone
     suffices. The derivation ends at the point where c5.2 is proved, since
     that establishes that Basis_2 is at least as powerful as Basis_1. $)

  $( Basis_2 --------------------------------------------- $)
  c6.2 $a |- `[ `[ ph `] `[ ps `] `] `[ `[ ph `] ps `] `= ph $.

  $( System_2 consequences ------------------------------------ $)

  $( An important lemma used in the proof of c1.2. $)
  lem2.2 $p |- `[ ph `] ph `= `[ ps `] ps $=
    wps lofdf-encl wps lofdf-juxt wph lofdf-encl wph lofdf-juxt wps lofdf-encl
    wph lofdf-encl lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wph
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wps wps lofdf-encl lofdf-void
    wph lofdf-encl wph lofdf-juxt wps wph lofdf-encl c6.2 wph lofdf-encl wps
    lofdf-encl lofdf-juxt wps lofdf-encl wph lofdf-encl lofdf-juxt lofdf-void
    lofdf-void wps lofdf-encl wps lofdf-encl wph lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-void wph lofdf-encl wph lofdf-juxt
    wph lofdf-encl wps lofdf-encl lofcmm wph lofdf-encl lofdf-encl wps
    lofdf-encl lofdf-juxt wps lofdf-encl wph lofdf-encl lofdf-encl lofdf-juxt
    lofdf-void lofdf-void wps lofdf-encl wph lofdf-encl wps lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-encl wph lofdf-juxt wph lofdf-encl
    lofdf-encl wps lofdf-encl lofcmm wps lofdf-encl lofdf-encl wph lofdf-encl
    lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl lofdf-encl wph lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl lofdf-void wph lofdf-encl
    lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wph lofdf-juxt
    wps lofdf-encl wph lofdf-encl c6.2 wph lofdf-encl wph lofdf-juxt wps
    lofdf-encl lofdf-encl wph lofdf-encl lofdf-encl lofdf-juxt lofdf-encl wps
    lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph
    lofdf-encl lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph
    lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl
    wph lofdf-juxt wps lofdf-encl lofdf-encl wph lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl wps lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt wps lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt wps lofdf-encl lofdf-encl wph lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl wps lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt wph lofdf-encl lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    wph lofdf-encl wph lofdf-juxt wps lofdf-encl lofdf-encl wph lofdf-encl
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl wps lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-juxt wps lofdf-encl lofdf-encl wph lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl wps lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt wps lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt
    lofdf-encl wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-juxt wph lofdf-encl lofdf-encl wps lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl wph lofdf-encl lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-juxt
    wph lofdf-encl wph lofdf-juxt wps lofdf-encl lofdf-encl wph lofdf-encl
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl wps lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-juxt wph lofdf-encl lofdf-encl wps lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl wps lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt wph lofdf-encl wph lofdf-encl wps lofdf-encl
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt wph wph lofdf-encl wps lofdf-encl c6.2 wph wps
    lofdf-encl c6.2 lofquad wph lofdf-encl lofdf-encl wps lofdf-encl lofdf-encl
    lofdf-juxt wps lofdf-encl lofdf-encl wph lofdf-encl lofdf-encl lofdf-juxt
    lofdf-void lofdf-void lofdf-void wph lofdf-encl lofdf-encl wps lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt wph lofdf-encl lofdf-encl wps lofdf-encl lofdf-encl lofcmm
    lofsubb1 lofeucr wph lofdf-encl wps lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl wps lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl
    wps lofdf-encl lofdf-encl wph lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-encl lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-encl lofdf-encl lofdf-juxt wps lofdf-encl lofdf-encl wph lofdf-encl
    lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-encl lofcmm lofbeq lofsubst
    loftrans wph lofdf-encl lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wps
    lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl
    lofdf-encl wph lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-void wph
    lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofcmmx loftrans lofsym
    lofrep lofrepbx lofrepbx lofrep lofsym $.
    $( [24-Sep-2015] $)

  $( This is axiom B3 from Meguire. $)
  b3.2 $p |- `[ ph `] ph `= `[ `] $=
    wph lofdf-void lem2.2 $.
    
  $( [18-Aug-2016] $)
  c1.2 $p |- `[ `[ ph `] `] `= ph $=
    wph lofdf-encl wph lofdf-encl lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-encl wph lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    wph lofdf-encl lofdf-encl wph wph lofdf-encl lofdf-encl wph lofdf-encl
    lofdf-juxt wph lofdf-encl wph lofdf-encl lofdf-encl lofdf-juxt lofdf-void
    lofdf-void wph lofdf-encl wph lofdf-encl lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl lofdf-void wph lofdf-encl lofdf-encl wph lofdf-encl lofdf-encl
    wph lofdf-encl lofcmm wph lofdf-encl lofdf-encl lofdf-encl wph lofdf-encl
    lofdf-juxt wph lofdf-encl wph lofdf-encl lofdf-encl lofdf-encl lofdf-juxt
    lofdf-void lofdf-void lofdf-void wph lofdf-encl lofdf-encl wph lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl wph lofdf-encl lofdf-encl
    lofdf-encl wph lofdf-encl lofcmm wph lofdf-encl lofdf-encl wph lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl lofdf-encl wph lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl lofdf-encl lofdf-encl wph
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl wph lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-void lofdf-void wph lofdf-encl
    lofdf-encl wph lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-encl lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl
    lofcmm wph lofdf-encl lofdf-encl lofdf-encl wph lofdf-encl lofdf-encl
    lofdf-juxt wph lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt lofdf-void
    lofdf-void lofdf-void wph lofdf-encl lofdf-encl lofdf-encl wph lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl wph lofdf-encl lofdf-encl
    wph lofdf-encl lem2.2 wph lofdf-encl lofdf-encl wph lofdf-encl c6.2
    lofrepbx lofrep lofrepbx lofrepbx wph wph lofdf-encl lofdf-encl c6.2
    lofeucr $.
    
  $( [25-Sep-2015] $)
  j1.2 $p |- `[ `[ ph `] ph `] `= $=
    wph lofdf-encl wph lofdf-juxt lofdf-encl lofdf-void lofdf-encl lofdf-encl
    lofdf-void wph lofdf-encl wph lofdf-juxt lofdf-void lofdf-encl wph b3.2
    lofbeq lofdf-void c1.2 loftrans $.
    
  $( [25-Sep-2015] $)
  lem3.2 $p |- `[ ph ph `] `= `[ `[ `[ ph `] `] `[ `[ ph `] `] `] $=
    wph lofdf-encl lofdf-encl wph lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    wph wph lofdf-juxt lofdf-encl wph wph lofdf-encl lofdf-encl wph lofdf-encl
    lofdf-encl lofdf-void lofdf-void lofdf-void wph wph lofdf-juxt lofdf-encl
    wph lofdf-encl lofdf-encl wph wph c1.2 lofsym wph wph lofdf-encl lofdf-encl
    lofdf-void wph lofdf-void lofdf-void wph wph lofdf-juxt lofdf-encl wph
    lofdf-encl lofdf-encl wph wph c1.2 lofsym wph wph lofdf-juxt lofdf-encl
    lofid lofrepbx lofrepbx lofsym $.
    
  $( [25-Sep-2015] $)
  c5.2 $p |- ph ph `= ph $=
    wph lofdf-encl lofdf-encl wph wph lofdf-juxt wph wph lofdf-encl lofdf-encl
    wph lofdf-encl lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl
    wph lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl lofdf-void
    lofdf-void lofdf-void lofdf-void wph wph lofdf-juxt wph lofdf-encl wph
    lofdf-encl c6.2 wph wph lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl wph
    lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-void wph lofdf-encl
    lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl lofdf-void lofdf-void wph
    wph lofdf-juxt wph lem3.2 lofdf-void wph lofdf-encl lofdf-encl wph
    lofdf-encl lofdf-juxt lofdf-encl wph wph lofdf-juxt lofdf-encl lofdf-void
    lofdf-void lofdf-void wph wph lofdf-juxt wph lofdf-encl lofdf-encl wph
    lofdf-encl lofdf-juxt lofdf-encl lofdf-void wph lofdf-encl j1.2 lofsym wph
    wph lofdf-juxt c1.2 lofrepbx lofrepbx lofrepbx wph c1.2 lofeucr $.
    $( [25-Sep-2015] $)

  $( =======================================================================

     System_3

     Deriving C6 from the Robbins equation, demonstrating that a Robbins
     algebra is a Boolean algebra. $)

  $( Basis_3 --------------------------------------------- $)

  $( The more familiar form of the Robbins equation is ((p q) (p (q)))
     ` = p, but for this exercise I'll be using the equivalent form: $)
  robbins $a |- `[ `[ `[ ph `] ps `] `[ ph ps `] `] `= ps $.

  $( System_3 consequences ------------------------------------ $)
  j1.3 $p |- `[ `[ ph `] ph `] `= $=
    wph lofdf-encl wph lofdf-juxt lofdf-encl wps lofdf-encl wph lofdf-juxt
    lofdf-encl wps wph lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-encl
    wps lofdf-encl wph lofdf-juxt lofdf-encl wps wph lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-void wph lofdf-encl wph
    lofdf-juxt wps lofdf-encl wph lofdf-juxt lofdf-encl wps wph lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lofdf-encl wps lofdf-encl wph lofdf-juxt
    lofdf-encl wps wph lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    wph lofdf-encl wps lofdf-encl wph lofdf-juxt lofdf-encl wps wph lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lofdf-encl wph wps lofdf-encl wph
    lofdf-juxt lofdf-encl wps wph lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    wph wps lofdf-encl wph lofdf-juxt lofdf-encl wps wph lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl wps lofdf-encl wph lofdf-juxt lofdf-encl wps wph
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wph wps wph robbins lofsym
    lofbeq wps lofdf-encl wph lofdf-juxt lofdf-encl wps wph lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl wph wps wph robbins lofsym lofquad lofbeq
    wps lofdf-encl wph lofdf-juxt lofdf-encl wps wph lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-void robbins loftrans $.
    
  $( [8-Dec-2016] $)
  c1.3 $p |- `[ `[ ph `] `] `= ph $=
    wph lofdf-encl lofdf-encl wph lofdf-juxt lofdf-encl lofdf-encl wph
    lofdf-encl lofdf-encl wph wph wph lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl lofdf-encl wph lofdf-encl lofdf-encl wph lofdf-juxt lofdf-encl
    lofdf-encl lofdf-void lofdf-void wph lofdf-encl lofdf-encl wph wph
    lofdf-encl lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl wph
    lofdf-juxt lofdf-encl wph wph lofdf-encl lofdf-encl lofdf-juxt wph
    lofdf-encl lofdf-encl wph lofdf-juxt wph wph lofdf-encl lofdf-encl lofcmm
    lofbeq lofbeq wph lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt
    lofdf-encl lofdf-void lofdf-void wph wph lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl lofdf-void lofdf-void wph lofdf-encl lofdf-encl wph lofdf-void
    robbins wph lofdf-encl wph lofdf-encl lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl lofdf-void wph
    wph lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-void lofdf-void wph
    lofdf-encl lofdf-encl wph lofdf-encl wph lofdf-encl lofdf-encl lofdf-juxt
    wph lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt wph lofdf-encl wph
    lofdf-encl lofdf-encl lofcmm lofbeq wph wph lofdf-encl lofdf-encl robbins
    lofrepbx lofrepbx lofrep wph lofdf-encl wph lofdf-juxt lofdf-encl
    lofdf-void wph lofdf-encl lofdf-encl wph lofdf-juxt lofdf-encl lofdf-void
    lofdf-void lofdf-void wph wph j1.3 wph lofdf-encl wph robbins lofrepbx
    lofeucr $.
    
  $( [8-Dec-2016] $)
  c6.3 $p |- `[ `[ ph `] `[ ps `] `] `[ `[ ph `] ps `] `= ph $=
    wps wph lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-juxt lofdf-void
    lofdf-void wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-void
    wph wps wph lofdf-encl lofcmm wps lofdf-encl wph lofdf-encl lofdf-juxt wph
    lofdf-encl wps lofdf-encl lofdf-juxt lofdf-void lofdf-void lofdf-void wps
    wph lofdf-encl lofdf-juxt lofdf-encl wph wps lofdf-encl wph lofdf-encl
    lofcmm wps lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl wps wph
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl lofdf-encl wph
    wps lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl wps wph lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-encl wps lofdf-encl wph
    lofdf-encl lofdf-juxt lofdf-encl wps wph lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt wph lofdf-encl lofdf-encl wps lofdf-encl wph lofdf-encl
    lofdf-juxt lofdf-encl wps wph lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    c1.3 wps lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl wps wph lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps wph
    lofdf-encl robbins lofbeq lofeucr wph c1.3 loftrans lofrepbx lofrepbx $.
    
  $( [5-Oct-2015] $)
  robblem1.3 $p |- `[ `[ `[ `[ ps `] `[ ph `] `] `[ ps `[ ph `] `] `] `]
                   `= `[ `[ ph `] `] $=
    wps lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl wps wph lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps wph
    lofdf-encl robbins lofbeq $.
    $( [31-Jan-2017] $)


  $( =======================================================================
     Topics in Laws of Form

     Associativity of logical connectives

     Since LoF lacks the concept of associativity, proving that a model of LoF
     has associative connectives may involve meta-reasoning.  For example, the
     proof of (p ze q) ze ch = ph ze (q ze r) corresponds to the equation 
     ph ps ch = ph ps      r, which is easy to prove in LoF!  Under the dual interpretation this also
     proves the associativity of conjunction, but here I will prove that more
     directly.  Since ph & ps corresponds to ((p)(q)), we need to show that
     ((((p)(q))) (r)) = ((p) (((q)(r)))).  Consider the left side of that
     equation -- it evaluates to ((p)(q)(r)), a form symmetric in the three
     variables: $)
  conj3 $p |- `[ `[ `[ `[ ph `] `[ ps `] `] `] `[ ch `] `]
              `= `[ `[ ph `] `[ ps `] `[ ch `] `] $=
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-encl wph
    lofdf-encl wps lofdf-encl lofdf-juxt lofdf-void wch lofdf-encl lofdf-void
    lofdf-void wph lofdf-encl wps lofdf-encl lofdf-juxt c1.0 lofsubb1 $.
    $( [29-Dec-2016] $)

  $( This shows that a permutation of variables in the LHS leaves the
     result unchanged. Specifically, ((((q)(r))) (p)), which is equal to
     ((p) (((q)(r)))) by commutation, will evaluate to the same form as
     ((((p)(q))) (r)). This completes the proof. I call this meta-reasoning
     because we're using an undefined, intuitive notion of symmetry. Below
     is the full-length formal proof. $)

  $( Associativity of conjunction. $)
  conj-assc $p |- `[ `[ `[ `[ ph `] `[ ps `] `] `] `[ ch `] `]
                  `= `[ `[ ph `] `[ `[ `[ ps `] `[ ch `] `] `] `]
            $=
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-encl wch
    lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wch lofdf-encl lofdf-juxt
    lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl
    wps lofdf-encl wch lofdf-encl lofdf-juxt lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-encl
    wch lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-encl
    lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wch
    lofdf-encl lofdf-juxt lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt
    lofdf-encl wph wps wch conj3 wps lofdf-encl wch lofdf-encl lofdf-juxt
    lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl
    wch lofdf-encl lofdf-juxt wph lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-encl wps lofdf-encl lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl
    wps wch wph conj3 wps lofdf-encl wch lofdf-encl lofdf-juxt wph lofdf-encl
    lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-juxt wch lofdf-encl
    lofdf-juxt lofdf-void lofdf-void lofdf-void lofdf-void wps lofdf-encl wch
    lofdf-encl lofdf-juxt wph lofdf-encl lofcmm lofsubb1 loftrans lofeuc wps
    lofdf-encl wch lofdf-encl lofdf-juxt lofdf-encl lofdf-encl wph lofdf-encl
    lofdf-juxt wph lofdf-encl wps lofdf-encl wch lofdf-encl lofdf-juxt
    lofdf-encl lofdf-encl lofdf-juxt wps lofdf-encl wch lofdf-encl lofdf-juxt
    lofdf-encl lofdf-encl wph lofdf-encl lofcmm lofbeq loftrans $.
    $( [29-Dec-2016] $)

  $( Now I turn to proving the associativity of the biconditional:  (p<->q)<->r
     = p<->(q<->r). I had earlier taken for granted that p<->q, transcribed as 
     (((p)q) ((q)p)), was equivalent to ((p)(q)) (p q). Here I prove it: $)
  bicond $p |- `[ `[ `[ ph `] ps `] `[ `[ ps `] ph `] `]
               `= `[ `[ ph `] `[ ps `] `] `[ ph ps `] $=
    wps wph lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wph lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl
    wps lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph wps lofdf-juxt
    lofdf-encl lofdf-juxt wps wph lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-encl wps lofdf-juxt lofdf-encl lofdf-void wps lofdf-encl wph
    lofdf-juxt lofdf-encl lofdf-void lofdf-void wps wph lofdf-encl lofdf-juxt
    wph lofdf-encl wps lofdf-juxt wps wph lofdf-encl lofcmm lofbeq lofsubb1 wps
    lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl
    wph lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wps wph lofdf-encl
    lofdf-juxt lofdf-encl wps lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph wps
    lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl lofdf-encl wph lofdf-encl
    lofdf-juxt lofdf-encl wps lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt
    wps wph lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wph lofdf-juxt
    lofdf-encl lofdf-juxt wps lofdf-encl lofdf-encl wps lofdf-void wph
    lofdf-encl lofdf-void wps lofdf-encl wph lofdf-juxt lofdf-encl wps c1.0
    lofsubb1 lofbeq lofdf-void lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl
    lofdf-void lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl
    lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl
    wph lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl lofdf-encl
    wph lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wph lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-encl lofdf-juxt
    lofdf-encl wph wps lofdf-juxt lofdf-encl lofdf-juxt lofdf-void lofdf-encl
    wph lofdf-encl lofdf-juxt lofdf-encl lofdf-void lofdf-encl wph lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-void lofdf-void wps lofdf-encl lofdf-encl wph
    lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wph lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-void lofdf-void lofdf-void wph c6.0 lofsubb1 lofdf-void
    lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl lofdf-encl
    wph lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wph
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-void lofdf-encl wph lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lofdf-void lofdf-encl wph lofdf-encl
    lofdf-juxt lofdf-encl lofdf-void lofdf-encl wph lofdf-juxt lofdf-encl
    lofdf-juxt wps lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt wps lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph wps lofdf-juxt
    lofdf-encl lofdf-juxt wps lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt
    lofdf-encl wps lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt lofdf-void
    lofdf-encl wph lofdf-juxt lofdf-encl lofdf-void lofdf-encl wph lofdf-encl
    lofdf-juxt lofdf-encl lofdf-void lofdf-void lofdf-void lofdf-void lofcmmbx
    wph lofdf-void wps lofdf-encl wps lofdf-void c9.0 lofeucr lofeucr lofeucr
    lofeucr $.
    $( [29-Dec-2016] $)

  $( Next I'll need the following two lemmas: $)
  c2lem1 $p |- `[ ps `[ ph ps `] ch `] `= `[ `[ ph `] ps ch `] $=
    wps wph wps lofdf-juxt lofdf-encl lofdf-juxt wch lofdf-juxt wph lofdf-encl
    wps lofdf-juxt wch lofdf-juxt wps wph wps lofdf-juxt lofdf-encl lofdf-juxt
    wch lofdf-juxt wph wps lofdf-juxt lofdf-encl wps lofdf-juxt wch lofdf-juxt
    wph lofdf-encl wps lofdf-juxt wch lofdf-juxt wps wph wps lofdf-juxt
    lofdf-encl lofdf-void lofdf-void wch lofcmmx wph wps lofdf-juxt lofdf-encl
    wps lofdf-juxt wph lofdf-encl wps lofdf-juxt wch wph wps c2.0 lofsub
    loftrans lofbeq $.
    
  $( [29-Dec-2016] $)
  c2lem2 $p |- `[ ph `[ ph ps `] ch `] `= `[ ph `[ ps `] ch `] $=
    wph wph wps lofdf-juxt lofdf-encl lofdf-juxt wch lofdf-juxt wph wps
    lofdf-encl lofdf-juxt wch lofdf-juxt wph wph wps lofdf-juxt lofdf-encl
    lofdf-juxt wch lofdf-juxt wps lofdf-encl wph lofdf-juxt wch lofdf-juxt wph
    wps lofdf-encl lofdf-juxt wch lofdf-juxt wph wph wps lofdf-juxt lofdf-encl
    lofdf-juxt wch lofdf-juxt wps wph lofdf-juxt lofdf-encl wph lofdf-juxt wch
    lofdf-juxt wps lofdf-encl wph lofdf-juxt wch lofdf-juxt wph wph wps
    lofdf-juxt lofdf-encl lofdf-juxt wch lofdf-juxt wph wps wph lofdf-juxt
    lofdf-encl lofdf-juxt wch lofdf-juxt wps wph lofdf-juxt lofdf-encl wph
    lofdf-juxt wch lofdf-juxt wph wps lofdf-void lofdf-void lofdf-void wph wch
    lofcmmbx wph wps wph lofdf-juxt lofdf-encl lofdf-void lofdf-void wch
    lofcmmx loftrans wps wph lofdf-juxt lofdf-encl wph lofdf-juxt wps
    lofdf-encl wph lofdf-juxt wch wps wph c2.0 lofsub loftrans wps lofdf-encl
    wph lofdf-void lofdf-void wch lofcmmx loftrans lofbeq $.
    $( [29-Dec-2016] $)

  $( Let A = p<->q <-> ((p)(q)) (p q) and B <-> q<->r <-> ((q)(r)) (q r).  
     Proving that the biconditional associates amounts to proving: ((A)(r))
     (A r) = ((p)(B)) (p B), i.e., ((((p)(q)) (p q))(r)) (((p)(q)) (p q) r) 
     = ((p)(((q)(r)) (q r))) (p ((q)(r)) (q r)). Consider the left side of 
     that equation -- as in the case of conjunction, it evaluates to a form 
     symmetric in the three variables: $)
  bic3 $p |- `[ `[ `[ `[ ph `] `[ ps `] `] `[ ph ps `] `] `[ ch `] `]
             `[ `[ `[ ph `] `[ ps `] `] `[ ph ps `] ch `]
             `= `[ `[ ph `] `[ ps `] `[ ch `] `] `[ ph ps `[ ch `] `]
                 `[ ph `[ ps `] ch `] `[ `[ ph `] ps ch `] $=
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph wps lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl wch lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph wps lofdf-juxt
    lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl
    wps lofdf-encl lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl wph wps
    lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph wps
    lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt wps wph wps
    lofdf-juxt lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt wph
    lofdf-encl wps lofdf-encl lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl
    wph wps lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph wps
    lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl
    wps lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps
    lofdf-encl lofdf-juxt lofdf-encl wph wps lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl wch lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-encl lofdf-juxt lofdf-encl wph wps lofdf-juxt lofdf-encl lofdf-juxt
    wch lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl
    lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl wph wps lofdf-juxt wch
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph wph wps lofdf-juxt
    lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl wps wph wps lofdf-juxt
    lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt lofdf-juxt wph
    lofdf-encl wps lofdf-encl lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl
    wph wps lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph wps
    lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl wps wph wps lofdf-juxt
    lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt lofdf-juxt wph
    lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph wps lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl wch lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-encl wps lofdf-encl lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl
    wph wps lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph
    lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph wps lofdf-juxt
    lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl wph wph wps lofdf-juxt
    lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl wps wph wps lofdf-juxt
    lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl
    wps lofdf-encl lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl wph wps
    lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    lofdf-encl wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph wps
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wch lofdf-encl lofdf-juxt
    lofdf-encl wph lofdf-encl wps lofdf-encl lofdf-juxt wch lofdf-encl
    lofdf-juxt lofdf-encl wph wps lofdf-juxt wch lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-juxt wch
    lofdf-encl lofdf-juxt lofdf-encl wph wps lofdf-juxt wch lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-encl
    lofdf-juxt lofdf-encl wph wps lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    wch lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-juxt wph wps
    lofdf-juxt wch lofdf-encl j2.0 lofbeq wph lofdf-encl wps lofdf-encl
    lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl wph wps lofdf-juxt wch
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt c1.0 lofeucr wph wph wps
    lofdf-juxt lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl wps wph wps
    lofdf-juxt lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lofdf-encl wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl
    wph wps lofdf-juxt lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl wph wph
    wps lofdf-juxt lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl wps wph wps
    lofdf-juxt lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt wph
    wph wps lofdf-juxt lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl wps wph
    wps lofdf-juxt lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph wps
    lofdf-juxt lofdf-encl lofdf-juxt wch lofdf-juxt wph wps wph wps lofdf-juxt
    lofdf-encl wch lofdf-juxt j2.0 lofbeq wph wph wps lofdf-juxt lofdf-encl
    lofdf-juxt wch lofdf-juxt lofdf-encl wps wph wps lofdf-juxt lofdf-encl
    lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt c1.0 lofeucr lofquad wph
    wph wps lofdf-juxt lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl wph wps
    lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-encl lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl wph wps
    lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wps wph wps
    lofdf-juxt lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl wph wps wch
    c2lem2 lofsubst loftrans wps wph wps lofdf-juxt lofdf-encl lofdf-juxt wch
    lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt wch lofdf-juxt
    lofdf-encl wph lofdf-encl wps lofdf-encl lofdf-juxt wch lofdf-encl
    lofdf-juxt lofdf-encl wph wps lofdf-juxt wch lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt wph wps lofdf-encl lofdf-juxt wch lofdf-juxt
    lofdf-encl lofdf-juxt wph wps wch c2lem1 lofsubr loftrans $.
    $( [29-Dec-2016] $)

  $( This completes the informal proof that the biconditional associates.
     Below is the formal proof.  First, we need a permuted version of bic3. $)
  bic3x $p |- `[ `[ `[ `[ ps `] `[ ch `] `] `[ ps ch `] `] `[ ph `] `]
              `[ `[ `[ ps `] `[ ch `] `] `[ ps ch `] ph `]
              `= `[ `[ ph `] `[ ps `] `[ ch `] `] `[ ph ps `[ ch `] `]
                  `[ ph `[ ps `] ch `] `[ `[ ph `] ps ch `] $=
    wps lofdf-encl wch lofdf-encl lofdf-juxt lofdf-encl wps wch lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl wps
    lofdf-encl wch lofdf-encl lofdf-juxt lofdf-encl wps wch lofdf-juxt
    lofdf-encl lofdf-juxt wph lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl
    wps lofdf-encl lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-encl wps lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt wph wps
    lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt wph wps
    lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl
    wps lofdf-encl lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl wph wps
    lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph wps
    lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl
    wps lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wch
    lofdf-encl lofdf-juxt lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wch
    lofdf-encl lofdf-juxt lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt
    wph lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl
    lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt wph wps lofdf-juxt wch
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph wps lofdf-encl lofdf-juxt
    wch lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl
    lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt wph wps lofdf-encl
    lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt wph wps lofdf-juxt wch
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wch lofdf-encl
    lofdf-juxt lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wch lofdf-encl
    lofdf-juxt lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt wph
    lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-juxt
    wch lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt wch
    lofdf-juxt lofdf-encl lofdf-juxt wph wps lofdf-juxt wch lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wch lofdf-juxt wph
    lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-juxt
    wch lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt wch
    lofdf-juxt lofdf-encl lofdf-juxt wph wps lofdf-juxt wch lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt wph wps lofdf-encl lofdf-juxt wch
    lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wch lofdf-encl lofdf-juxt
    lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wch lofdf-encl lofdf-juxt
    lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-juxt
    lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-juxt wch
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt wch
    lofdf-juxt lofdf-encl lofdf-juxt wps wch lofdf-encl lofdf-juxt wph
    lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wch lofdf-juxt wph
    lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-juxt
    wch lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt wch
    lofdf-juxt lofdf-encl lofdf-juxt wph wps lofdf-juxt wch lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wch lofdf-juxt wph
    lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wch lofdf-encl lofdf-juxt
    lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wch lofdf-encl lofdf-juxt
    lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-juxt
    lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-juxt wch
    lofdf-encl lofdf-juxt lofdf-encl wps wch lofdf-juxt wph lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt wps wch lofdf-encl lofdf-juxt wph
    lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wch lofdf-juxt wph
    lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-juxt
    wch lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt wch
    lofdf-juxt lofdf-encl lofdf-juxt wps wch lofdf-encl lofdf-juxt wph
    lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wch lofdf-juxt wph
    lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wch lofdf-encl lofdf-juxt
    lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wch lofdf-encl lofdf-juxt
    lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-juxt
    lofdf-encl lofdf-juxt wps lofdf-encl wch lofdf-encl lofdf-juxt wph
    lofdf-encl lofdf-juxt lofdf-encl wps wch lofdf-juxt wph lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt wps wch lofdf-encl lofdf-juxt wph
    lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wch lofdf-juxt wph
    lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-juxt
    wch lofdf-encl lofdf-juxt lofdf-encl wps wch lofdf-juxt wph lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt wps wch lofdf-encl lofdf-juxt wph
    lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wch lofdf-juxt wph
    lofdf-juxt lofdf-encl lofdf-juxt wps wch wph bic3 wps lofdf-encl wch
    lofdf-encl lofdf-juxt wph lofdf-encl lofdf-void lofdf-void lofdf-void
    lofdf-void wps wch lofdf-juxt wph lofdf-encl lofdf-juxt lofdf-encl wps wch
    lofdf-encl lofdf-juxt wph lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl
    wch lofdf-juxt wph lofdf-juxt lofdf-encl lofdf-juxt lofcmmbx loftrans wps
    wch lofdf-juxt wph lofdf-encl lofdf-void lofdf-void lofdf-void wph
    lofdf-encl wps lofdf-encl lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl
    wps wch lofdf-encl lofdf-juxt wph lofdf-juxt lofdf-encl wps lofdf-encl wch
    lofdf-juxt wph lofdf-juxt lofdf-encl lofdf-juxt lofcmmbx loftrans wps wch
    lofdf-encl lofdf-juxt wph lofdf-void lofdf-void lofdf-void wph lofdf-encl
    wps lofdf-encl lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-encl wps lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt wps
    lofdf-encl wch lofdf-juxt wph lofdf-juxt lofdf-encl lofcmmbx loftrans wps
    lofdf-encl wch lofdf-juxt wph lofdf-void lofdf-void lofdf-void wph
    lofdf-encl wps lofdf-encl lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-encl wps lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt wph wps
    lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-void
    lofcmmbx loftrans wph wps lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl
    wph wps lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-encl lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl
    wps lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt lofdf-void lofdf-void
    lofcmmx loftrans wph lofdf-encl wps lofdf-juxt wch lofdf-juxt lofdf-encl
    wph wps lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-encl lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl wph wps
    lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-void lofcmmx loftrans
    $.
    $( [29-Dec-2016] $)

  $( The associativity of the biconditional. $)
  bicond-assc $p |- `[ `[ `[ `[ ph `] `[ ps `] `] `[ ph ps `] `] `[ ch `] `]
                    `[ `[ `[ ph `] `[ ps `] `] `[ ph ps `] ch `]
                    `= `[ `[ ph `] `[ `[ `[ ps `] `[ ch `] `] `[ ps ch `] `] `]
                        `[ ph `[ `[ ps `] `[ ch `] `] `[ ps ch `] `] $=
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph wps lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl wch lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph wps lofdf-juxt
    lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl
    wch lofdf-encl lofdf-juxt lofdf-encl wps wch lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl
    wch lofdf-encl lofdf-juxt lofdf-encl wps wch lofdf-juxt lofdf-encl
    lofdf-juxt wph lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps
    lofdf-encl wch lofdf-encl lofdf-juxt lofdf-encl wps wch lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wph wps lofdf-encl
    wch lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wps wch lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl
    lofdf-juxt lofdf-encl wph wps lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    wch lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-encl
    lofdf-juxt lofdf-encl wph wps lofdf-juxt lofdf-encl lofdf-juxt wch
    lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl lofdf-juxt
    wch lofdf-encl lofdf-juxt lofdf-encl wph wps lofdf-juxt wch lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt wph wps lofdf-encl lofdf-juxt wch
    lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-juxt wch
    lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wch lofdf-encl lofdf-juxt
    lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wch lofdf-encl lofdf-juxt
    lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-juxt
    lofdf-encl lofdf-juxt wph wps wch bic3 wph wps wch bic3x lofeuc wps
    lofdf-encl wch lofdf-encl lofdf-juxt lofdf-encl wps wch lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl wps
    lofdf-encl wch lofdf-encl lofdf-juxt lofdf-encl wps wch lofdf-juxt
    lofdf-encl lofdf-juxt wph lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl
    wps lofdf-encl wch lofdf-encl lofdf-juxt lofdf-encl wps wch lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wch
    lofdf-encl lofdf-juxt lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt
    wph lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-encl wch
    lofdf-encl lofdf-juxt lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl wph wps lofdf-encl wch lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt wps wch lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt wps lofdf-encl wch lofdf-encl lofdf-juxt lofdf-encl
    wps wch lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl
    lofdf-void lofdf-void lofdf-void lofdf-void wps lofdf-encl wch lofdf-encl
    lofdf-juxt lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt wph
    lofdf-juxt lofdf-encl lofcmmbx wps lofdf-encl wch lofdf-encl lofdf-juxt
    lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-void
    lofdf-void lofdf-void wph lofdf-encl wps lofdf-encl wch lofdf-encl
    lofdf-juxt lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl lofdf-void lofcmmbx loftrans loftrans $.
    $( [29-Dec-2016] $)



  
  
  $( Versions of C1. $)

  lofc1r $p |- ph `= `[ `[ ph `] `] $=
    wph lofdf-encl lofdf-encl  wph
    wph c1.0 lofsym  $.

  lofc1x $p |- et `[ `[ ph `] `] ze `= et ph ze $=
    wph lofdf-encl lofdf-encl  wph
    wet wze
    wph c1.0 
    lofsubst  $.

  lofc1rx $p |-  et ph ze `=  et `[ `[ ph `] `] ze  $=
    wph  wph lofdf-encl lofdf-encl
    wet wze
    wph lofc1r
    lofsubst   $.

  lofc1bx $p |- si `[ et `[ `[ ph `] `] ze `] rh `= si `[ et ph ze `] rh $=
    wet wph lofdf-encl lofdf-encl lofdf-juxt wze lofdf-juxt
    wet wph lofdf-juxt wze lofdf-juxt
    lofdf-void lofdf-void
    wsi wrh
    wph wet wze lofc1x
    lofsubb1  $.

  lofc1rbx $p |- si `[ et ph ze `] rh `=  si `[ et `[ `[ ph `] `] ze `] rh  $=
    wsi wet wph lofdf-encl lofdf-encl lofdf-juxt wze lofdf-juxt lofdf-encl
    lofdf-juxt wrh lofdf-juxt
    wsi wet wph lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt wrh lofdf-juxt
    wph wet wze wsi wrh  lofc1bx lofsym  $.
  
  $( Versions of C2. $)
  lofc2x $p |- et `[ ph ps ze `] si ps rh `= et `[ ph ze `] si ps rh $= 

    wet wph wze lofdf-juxt lofdf-encl lofdf-juxt wsi
    lofdf-juxt wps lofdf-juxt wrh lofdf-juxt

    wet wph wps lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt wsi
    lofdf-juxt wps lofdf-juxt wrh lofdf-juxt

    wps wsi lofdf-juxt
    wsi wps lofdf-juxt
    wet wph wze lofdf-juxt lofdf-encl lofdf-juxt
    wrh
    wet wph wps lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt wsi
    lofdf-juxt wps lofdf-juxt wrh lofdf-juxt

    wps wsi lofcmm
    
    wph wze lofdf-juxt wps lofdf-juxt lofdf-encl wps lofdf-juxt
    wph wze lofdf-juxt lofdf-encl wps lofdf-juxt
    wet
    wsi wrh lofdf-juxt
    wet wph wps lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt wsi
    lofdf-juxt wps lofdf-juxt wrh lofdf-juxt

    wph wze lofdf-juxt   wps
    c2.0

    wet wph wps lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt wsi
    lofdf-juxt wps lofdf-juxt wrh lofdf-juxt

    wet wph wze lofdf-juxt wps lofdf-juxt lofdf-encl lofdf-juxt wps
    lofdf-juxt wsi lofdf-juxt wrh lofdf-juxt

    wet wph wps lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt wsi
    lofdf-juxt wps lofdf-juxt wrh lofdf-juxt

    wet wph wze lofdf-juxt wps lofdf-juxt lofdf-encl lofdf-juxt wsi
    lofdf-juxt wps lofdf-juxt wrh lofdf-juxt

    wet wph wze lofdf-juxt wps lofdf-juxt lofdf-encl lofdf-juxt wps
    lofdf-juxt wsi lofdf-juxt wrh lofdf-juxt

    wps wze wph lofdf-void lofdf-void wet wsi wps lofdf-juxt wrh lofdf-juxt
    lofcmmbx
    
    wsi wps   wet wph wze lofdf-juxt wps lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-void wrh
    lofcmmx
    loftrans
    lofsym

    lofrep
    lofrep
    lofsym
    $.

  lofc2bx $p |- mu `[ et `[ ph ps ze `] si ps rh `] la
                `= mu `[ et `[ ph ze `] si ps rh `] la $=
    wet wph wps lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt
    wsi lofdf-juxt wps lofdf-juxt wrh lofdf-juxt
    wet wph wze lofdf-juxt lofdf-encl lofdf-juxt
    wsi lofdf-juxt wps lofdf-juxt wrh lofdf-juxt
    lofdf-void lofdf-void wmu wla
    wph wps wet wze wsi wrh
    lofc2x
    lofsubb1 $.

  lofc2rx $p |-  et ps ze `[ ph ps si `] rh `= et ps ze `[ ph si `] rh $=
       
    wet wps lofdf-juxt wze lofdf-juxt  wph wps lofdf-juxt wsi lofdf-juxt
    lofdf-encl lofdf-juxt wrh lofdf-juxt

    wet wph  wsi lofdf-juxt lofdf-encl lofdf-juxt
    wps lofdf-juxt wze lofdf-juxt wrh lofdf-juxt

    wet wps lofdf-juxt wze lofdf-juxt  wph  wsi lofdf-juxt
    lofdf-encl lofdf-juxt wrh lofdf-juxt

    wet wps lofdf-juxt wze lofdf-juxt  wph wps lofdf-juxt wsi lofdf-juxt
    lofdf-encl lofdf-juxt wrh lofdf-juxt

    wet wph wps lofdf-juxt wsi lofdf-juxt lofdf-encl lofdf-juxt
    wps lofdf-juxt wze lofdf-juxt wrh lofdf-juxt

    wet wph  wsi lofdf-juxt lofdf-encl lofdf-juxt
    wps lofdf-juxt wze lofdf-juxt wrh lofdf-juxt

    wps wze lofdf-juxt
    wph wps lofdf-juxt wsi lofdf-juxt lofdf-encl
    wet
    lofdf-void
    wrh
    lofcmmx   
    
    wph wps wet wsi lofdf-void wze wrh lofdf-juxt
    lofc2x
    loftrans
    
    wph wsi lofdf-juxt lofdf-encl
    wps wze lofdf-juxt
    wet
    lofdf-void
    wrh
    lofcmmx
    loftrans
     $.

  lofc2rbx $p |- mu `[ et `[ ph ze `] si ps rh `] la
                 `= mu `[ et `[ ph ps ze `] si ps rh `] la $=
    wmu wet wph wps lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt
    wsi lofdf-juxt wps lofdf-juxt wrh lofdf-juxt lofdf-encl lofdf-juxt
    wla lofdf-juxt
    wmu wet wph wze lofdf-juxt lofdf-encl lofdf-juxt
    wsi lofdf-juxt wps lofdf-juxt wrh lofdf-juxt lofdf-encl lofdf-juxt
    wla lofdf-juxt
    wph wps wet wze wsi wrh wmu wla
    lofc2bx
    lofsym $.

  lofc2e $p |-  et `[ ph `] ze ph si `=  `[ `]  $=

    wet wph lofdf-encl lofdf-juxt wze lofdf-juxt wph lofdf-juxt wsi lofdf-juxt
    wet lofdf-void lofdf-encl lofdf-juxt wze lofdf-juxt wph lofdf-juxt wsi lofdf-juxt
    lofdf-void lofdf-encl

    lofdf-void wph wet lofdf-void wze wsi
    lofc2x
    
    wet lofdf-void lofdf-encl lofdf-juxt wze lofdf-juxt wph lofdf-juxt wsi lofdf-juxt
    lofdf-void lofdf-encl wet lofdf-juxt wze lofdf-juxt wph lofdf-juxt wsi lofdf-juxt
    lofdf-void lofdf-encl
    wet lofdf-void lofdf-encl lofdf-void lofdf-void
    wze wph lofdf-juxt wsi lofdf-juxt
    lofcmmx
    wet wze lofdf-juxt wph lofdf-juxt wsi lofdf-juxt
    c3.0
    loftrans
    loftrans
    $.
  
  $( Versions of C3. $)
  lofc3x $p |- ph `[ `] ps `= `[ `]  $= 
    wph lofdf-void lofdf-encl lofdf-juxt wps lofdf-juxt
    lofdf-void lofdf-encl wps lofdf-juxt wph lofdf-juxt
    lofdf-void lofdf-encl

    wph lofdf-void lofdf-encl wps lofdf-juxt lofcmm 
    wps wph lofdf-juxt c3.0

    loftrans
    $.

  lofc3bx $p |- et `[ ph `[ `] ps `] ze `= et ze  $=
    
    wet wph lofdf-void lofdf-encl lofdf-juxt wps lofdf-juxt lofdf-encl
    lofdf-juxt wze lofdf-juxt
    wet lofdf-void lofdf-encl lofdf-encl lofdf-juxt wze lofdf-juxt
    wet wze lofdf-juxt
    
    wph lofdf-void lofdf-encl lofdf-juxt wps lofdf-juxt
    lofdf-void lofdf-encl
    lofdf-void lofdf-void wet wze
    wph wps
    lofc3x
    lofsubb1

    lofdf-void wet wze
    lofc1x
    loftrans 
    $.

  $( Versions of C4. $)
  lofc4x $p |- si `[ et `[ ph `] ze `] rh ph mu `= si ph rh mu $=

    wsi wet wph lofdf-encl lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt
    wrh lofdf-juxt wph lofdf-juxt wmu lofdf-juxt

    wsi wph lofdf-encl wet lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt
    wph lofdf-juxt wrh lofdf-juxt wmu lofdf-juxt

    wsi wph lofdf-juxt wrh lofdf-juxt wmu lofdf-juxt

    
    wsi wet wph lofdf-encl lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt
    wrh lofdf-juxt wph lofdf-juxt wmu lofdf-juxt

    wsi wph lofdf-encl wet lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt
    wrh lofdf-juxt wph lofdf-juxt wmu lofdf-juxt

    wsi wph lofdf-encl wet lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt
    wph lofdf-juxt wrh lofdf-juxt wmu lofdf-juxt

    wet wph lofdf-encl lofdf-void lofdf-void wze wsi
    wrh wph lofdf-juxt wmu lofdf-juxt
    lofcmmbx  
    
    wrh wph
    wsi wph lofdf-encl wet lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-void wmu
    lofcmmx
    loftrans
    
    wph lofdf-encl wet lofdf-juxt wze lofdf-juxt lofdf-encl wph lofdf-juxt
    wph
    wsi
    wrh wmu lofdf-juxt
    wsi wph lofdf-encl wet lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt
    wph lofdf-juxt wrh lofdf-juxt wmu lofdf-juxt

    wph wet wze lofdf-juxt c4.0

    wsi wph lofdf-encl wet lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt
    wph lofdf-juxt wrh lofdf-juxt wmu lofdf-juxt
    lofid

    lofrep
    lofeuc
    $.

  lofc4rx $p |- si ph rh mu `= si `[ et `[ ph `] ze `] rh ph mu $=
    wsi wet wph lofdf-encl lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt
    wrh lofdf-juxt wph lofdf-juxt wmu lofdf-juxt
    wsi wph lofdf-juxt wrh lofdf-juxt wmu lofdf-juxt
    wph wet wze wsi wrh wmu
    lofc4x
    lofsym
    $.

  $( Versions of C5. $)
  lofc5x $p |- et ph ze ph si `= et ph ze si  $=
                
    wet wph lofdf-juxt wze lofdf-juxt wph lofdf-juxt wsi lofdf-juxt
    wet wph lofdf-juxt wph lofdf-juxt wze lofdf-juxt wsi lofdf-juxt
    wet wph lofdf-juxt wze lofdf-juxt wsi lofdf-juxt

    wze wph wet wph lofdf-juxt lofdf-void wsi
    lofcmmx

    wph wph lofdf-juxt   wph
    wet   wze wsi lofdf-juxt
    wet wph lofdf-juxt wph lofdf-juxt wze lofdf-juxt wsi lofdf-juxt
    wph c5.0
    wet wph lofdf-juxt wph lofdf-juxt wze lofdf-juxt wsi lofdf-juxt
    lofid
    lofrep
    lofeuc
    $.

  lofc5rx $p |- et ph ze si `= et ph ze ph si $=
    wet wph lofdf-juxt wze lofdf-juxt wph lofdf-juxt wsi lofdf-juxt
    wet wph lofdf-juxt wze lofdf-juxt wsi lofdf-juxt
    wph wet wze wsi  lofc5x
    lofsym
    $.

  $( Versions of J1. $)
  lofj1x $p |-   rh `[ et `[ ph `] ze ph si `] mu `= rh mu $=
                 
    wrh wet wph lofdf-encl lofdf-juxt wze lofdf-juxt wph lofdf-juxt
    wsi lofdf-juxt lofdf-encl lofdf-juxt wmu lofdf-juxt
    wrh wet lofdf-void lofdf-encl lofdf-juxt wze lofdf-juxt wph lofdf-juxt
    wsi lofdf-juxt lofdf-encl lofdf-juxt wmu lofdf-juxt
    wrh wmu lofdf-juxt

    lofdf-void wph wet lofdf-void wze wsi wrh wmu
    lofc2bx
    
    wet wze wph lofdf-juxt wsi lofdf-juxt wrh wmu
    lofc3bx
    loftrans
    $.

  lofj1rx $p |- rh mu `= rh `[ et `[ ph `] ze ph si `] mu $=
    wrh wet wph lofdf-encl lofdf-juxt wze lofdf-juxt wph lofdf-juxt
    wsi lofdf-juxt lofdf-encl lofdf-juxt wmu lofdf-juxt
    wrh wmu lofdf-juxt
    wph wet wze wsi wrh wmu 
    lofj1x
    lofsym
    $.

  $( Versions of J2. $)
  lofj2x $p |- et `[ `[ ph ch `] `[ ps ch `] `] ze si
               `= et `[ `[ ph `] `[ ps `] `] ze ch si $=    

    wet wph wch lofdf-juxt lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt wze lofdf-juxt wsi lofdf-juxt
    wet wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    wch lofdf-juxt wze lofdf-juxt wsi lofdf-juxt
    wet wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    wze lofdf-juxt wch lofdf-juxt wsi lofdf-juxt

    wph wch lofdf-juxt lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wch lofdf-juxt
    wet wze wsi lofdf-juxt
    wph wps wch          
    j2.0
    lofsubst
    
    wch wze
    wet wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-void
    wsi
    lofcmmx
    loftrans
    $.

  lofj2rx $p |- et `[ `[ ph `] `[ ps `] `] ze ch si
                `= et `[ `[ ph ch `] `[ ps ch `] `] ze si $=
    
    wet wph wch lofdf-juxt lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt wze lofdf-juxt wsi lofdf-juxt
    wet wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    wze lofdf-juxt wch lofdf-juxt wsi lofdf-juxt
    
    wph wps wch wet wze wsi
    lofj2x
    lofsym
    $.

    $( ---------------- MIXED THEOREMS ----------------- $)
  lofelimeq $p |- `[ `[ ph `] `[ `[ `] `] `] `[ ph `[ `] `] `= ph $=
    wph lofdf-encl lofdf-void lofdf-encl lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-void lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-void
    lofdf-encl lofdf-encl wph lofdf-juxt wph wph lofdf-encl lofdf-void
    lofdf-encl lofdf-encl lofdf-juxt lofdf-encl wph lofdf-void lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-void lofdf-encl wph lofdf-juxt
    lofdf-encl wph lofdf-juxt lofdf-void lofdf-encl lofdf-encl wph lofdf-juxt
    wph lofdf-encl lofdf-void lofdf-encl lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-void lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-void
    lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt lofdf-void lofdf-encl wph
    lofdf-juxt lofdf-encl wph lofdf-juxt wph lofdf-encl lofdf-void lofdf-encl
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-void lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt wph wph lofdf-void lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt wph lofdf-void lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt
    wph lofdf-encl lofdf-void lofdf-encl lofdf-encl lofdf-juxt lofdf-encl wph
    lofdf-void lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl
    lofdf-encl wph lofdf-void lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph
    wph lofdf-void lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-void
    lofdf-encl lofdf-encl lofdf-void wph lofdf-encl lofdf-void lofdf-void wph
    lofdf-void lofdf-encl lofdf-juxt lofdf-encl i2.1 lofsubb1 wph lofdf-encl
    lofdf-encl wph lofdf-void wph lofdf-void lofdf-encl lofdf-juxt lofdf-encl
    wph c1.0 lofsubst loftrans wph lofdf-void lofdf-encl lofdf-void lofdf-void
    lofdf-void wph lofdf-void lofcmmbx loftrans wph lofdf-void lofdf-encl wph
    lofdf-juxt lofdf-encl lofcmm loftrans lofdf-void lofdf-encl wph c2.0
    loftrans lofdf-void lofdf-encl lofdf-encl lofdf-void lofdf-void wph i2.1
    lofsubst loftrans $.
    $( [29-Jan-2017] $)


  $( LoF Deduction Theorems $)

  ${
    lofax-ded.1 $e |- ph `= ps $.
    lofax-ded.2 $e |- ph $.
    lofax-ded   $a |- ps $.
  $}

  ${
    lofelim.1 $e |- ph `= `[ `] $.
    $( If ` ph ` equals the marked state (i.e., truth), we can assert ` ph ` . $)
    lofelim   $p |- ph $=
    wph lofdf-encl lofdf-void lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-void lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    wph
    wph lofelimeq
    wph lofdf-void lofdf-encl
    lofelim.1
    lofdf-NtoU
    lofax-ded
    $.
  $}

  ${
    lofintr.1 $e |- ph $.
    $( If we can assert ` ph ` , then we can assert ` ph `= `[ `] ` 
       (i.e., ` ph ` is true). $)
    lofintr   $p |- ph `= `[ `]  $=
    wph lofdf-void lofdf-encl
    wph
    wph lofdf-encl lofdf-void lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-void lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    wph lofdf-encl lofdf-void lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-void lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    wph
    wph lofelimeq lofsym
    lofintr.1
    lofax-ded
    lofdf-UtoN
    $.
  $}

  ${
    lofeucrelim.1 $e |- ph `= ps $.
    lofeucrelim.2 $e |- ph `= `[ `] $.
    lofeucrelim   $p |- ps $=
      wps
      wph wps lofdf-void lofdf-encl
      lofeucrelim.1 lofeucrelim.2 lofeucr
      lofelim
    $.
  $}

  ${
    loftranselim.1 $e |- ph `= ps $.
    loftranselim.2 $e |- ps `= `[ `] $.
    loftranselim   $p |- ph $=
      wph
      wph wps lofdf-void lofdf-encl
      loftranselim.1 loftranselim.2 loftrans
      lofelim
    $.
  $}  

  ${
    lofand.1 $e |- ph $.
    lofand.2 $e |- ps $.
    lofand   $p |- `[ `[ ph `] `[ ps `] `] $=

    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl

    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl
    lofdf-void lofdf-encl wps lofdf-juxt lofdf-encl lofdf-juxt
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl
    lofdf-void lofdf-encl

    lofdf-void wps
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl
    lofdf-void
    lofc3bx
    
    wph lofdf-void lofdf-encl
    lofdf-void wps
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl
    lofdf-void
    lofdf-void lofdf-encl
    wph lofand.1 lofintr
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl
    wph wps lofdf-juxt lofdf-encl lofdf-juxt
    wph wps
    wph lofdf-void lofdf-encl wps
    wph lofand.1 lofintr
    wps lofand.2 lofintr
    lofeuc
    lofdf-NtoU
    lofintr
    lofrepbx
    
    lofeucr
    lofelim
    $.
  $}

  ${
    lofmp.1 $e |- `[ ph `] ps $.
    lofmp.2 $e |- ph $.
    lofmp   $p |- ps  $=
    wps
    wps lofdf-encl lofdf-encl  wps  lofdf-void lofdf-encl

    wps c1.0

    lofdf-void lofdf-encl lofdf-encl    lofdf-void
    wps lofdf-encl   lofdf-void   lofdf-void   lofdf-void
    lofdf-void lofdf-encl

    lofdf-void c1.0 

    wph lofdf-encl  lofdf-void lofdf-encl lofdf-encl
    wps lofdf-encl lofdf-void lofdf-void lofdf-void lofdf-void lofdf-encl
    

    wph lofdf-void lofdf-encl wph lofmp.2 lofintr lofbeq

    
    wph lofdf-encl wps lofdf-juxt lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl
    wps lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl
    lofdf-void lofdf-encl

    lofdf-void    wph lofdf-encl   lofdf-void  wps   lofdf-void   lofdf-void
    lofdf-void    lofdf-void
    lofc2bx
    
    wph lofdf-encl wps lofdf-juxt lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-encl wps lofdf-juxt
    wph
    lofmp.1 lofmp.2
    lofand
    lofintr
    lofeucr
    lofrepbx
    lofrepbx
    lofeucr
    lofelim
    $.
  $}

  $( ---------------- PROPOSITIONAL LOGIC ---------------- $)

  $( Declare the primitive constant symbols for propositional calculus. $)
  $c ( $.  $( Left parenthesis $)
  $c ) $.  $( Right parenthesis $)
  $c -> $. $( Right arrow (read:  "implies") $)
  $c -. $. $( Right handle (read:  "not") $)
  
  $( PLEASE PUT DESCRIPTION HERE. $)
  wi $a wff ( ph -> ps ) $.
  $( PLEASE PUT DESCRIPTION HERE. $)
  wn $a wff -. ph $.

  
  $( Define classical implication in terms of LoF. $)
  lofdf-imp $a |- ( ph -> ps ) `= `[ ph `] ps $.


  $( Define classical negation in terms of LoF. $)
  lofdf-neg $a |- -. ph `= `[ ph `] $.

  
  ax-1 $p |- ( ph -> ( ps -> ph ) ) $=
    wph wps wph wi wi
    
    wph wps wph wi wi
    wph lofdf-encl wps lofdf-encl lofdf-juxt wph lofdf-juxt
    lofdf-void lofdf-encl

    wph wps wph wi wi
    wph lofdf-encl wps wph wi lofdf-juxt
    wph lofdf-encl wps lofdf-encl lofdf-juxt wph lofdf-juxt
    wph wps wph wi
    lofdf-imp 
    
    wps wph wi   wps lofdf-encl wph lofdf-juxt
    wph lofdf-encl
    wps wph lofdf-imp
    lofsubr
    loftrans

    wph lofdf-void wps lofdf-encl lofdf-void
    lofc2e
    loftrans
    lofelim
    $.

  ax-2 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    wph wps wch wi wi wph wps wi wph wch wi wi wi

    wph wps wch wi wi wph wps wi wph wch wi wi wi
    wph lofdf-encl wps lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl
      wph  lofdf-encl lofdf-juxt wps lofdf-encl lofdf-juxt
      wch lofdf-juxt
    lofdf-void lofdf-encl

    wph wps wch wi wi wph wps wi wph wch wi wi wi
    wph lofdf-encl wps lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl
      wps  lofdf-encl lofdf-juxt wph lofdf-encl lofdf-juxt
      wch lofdf-juxt
    wph lofdf-encl wps lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl
      wph  lofdf-encl lofdf-juxt wps lofdf-encl lofdf-juxt
      wch lofdf-juxt


    wph wps wch wi wi wph wps wi wph wch wi wi wi
    wph lofdf-encl wps lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl
      wph lofdf-encl wps lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl lofdf-juxt
      wch lofdf-juxt
    wph lofdf-encl wps lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl
      wps  lofdf-encl lofdf-juxt wph lofdf-encl lofdf-juxt
      wch lofdf-juxt

    wps wch wi
    wps lofdf-encl wch lofdf-juxt
    wph lofdf-encl
    lofdf-void lofdf-void
    wph lofdf-encl wps lofdf-juxt lofdf-encl wph lofdf-encl lofdf-juxt wch lofdf-juxt
    wph wps wch wi wi wph wps wi wph wch wi wi wi

    wps wch lofdf-imp

    wph wps wch wi wi
    wph lofdf-encl wps wch wi lofdf-juxt
    lofdf-void lofdf-void lofdf-void
    wph lofdf-encl wps lofdf-juxt lofdf-encl wph lofdf-encl lofdf-juxt wch lofdf-juxt
    wph wps wch wi wi wph wps wi wph wch wi wi wi

    wph wps wch wi  lofdf-imp

    wph wps wi
    wph lofdf-encl wps lofdf-juxt
    lofdf-void lofdf-void
    wph wps wch wi wi lofdf-encl
    wph lofdf-encl wch lofdf-juxt
    wph wps wch wi wi wph wps wi wph wch wi wi wi

    wph wps lofdf-imp
    

    wph wch wi      wph lofdf-encl wch lofdf-juxt
    wph wps wch wi wi lofdf-encl wph wps wi lofdf-encl lofdf-juxt
    lofdf-void
    wph wps wch wi wi wph wps wi wph wch wi wi wi

    wph wch lofdf-imp

    wph wps wi   wph wch wi  wi
    wph wps wi lofdf-encl wph wch wi lofdf-juxt
    wph wps wch wi wi lofdf-encl
    lofdf-void
    wph wps wch wi wi wph wps wi wph wch wi wi wi
    
    wph wps wi   wph wch wi 
    lofdf-imp
       
    wph wps wch wi wi
    wph wps wi wph wch wi wi
    lofdf-imp
    
     lofreps
     lofreps
     lofrepbxs
     lofrepbxs
     lofrepbxs
    
    lofdf-void wph lofdf-encl
    wph lofdf-encl wps lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl
    wps lofdf-void wch
    lofc2x

    loftrans
    
    wps lofdf-encl   wph lofdf-encl
    wph lofdf-encl wps lofdf-encl lofdf-juxt wch lofdf-juxt lofdf-encl
    lofdf-void
    wch
    lofcmmx

    loftrans
    
    wph lofdf-encl wps lofdf-encl lofdf-juxt wch lofdf-juxt
    lofdf-void lofdf-void lofdf-void
    lofc2e

    loftrans
    lofelim
    $.

  ax-3 $p |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) )
       $=
    wph wn wps wn wi wps wph wi wi

    wph wn wps wn wi wps wph wi wi
    wph lofdf-encl wps lofdf-encl lofdf-juxt wph lofdf-juxt
    lofdf-void lofdf-encl
    
    wph wn wps wn wi wps wph wi wi
    wph lofdf-encl lofdf-encl lofdf-encl wps lofdf-encl lofdf-juxt wph lofdf-juxt
    wph lofdf-encl wps lofdf-encl lofdf-juxt wph lofdf-juxt

    wph wn wps wn wi wps wph wi wi
    wph lofdf-encl lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl
      wps lofdf-encl lofdf-juxt wph lofdf-juxt
    wph lofdf-encl lofdf-encl lofdf-encl wps lofdf-encl lofdf-juxt wph lofdf-juxt

    wps wn
    wps lofdf-encl
    wph lofdf-encl lofdf-encl
    lofdf-void
    lofdf-void
    wps lofdf-encl wph lofdf-juxt
    wph wn wps wn wi wps wph wi wi

    wps lofdf-neg

    wph wn lofdf-encl
    wph lofdf-encl lofdf-encl
    lofdf-void
    wps wn
    lofdf-void
    wps lofdf-encl wph lofdf-juxt
    wph wn wps wn wi wps wph wi wi

    wph wn wph lofdf-encl   
    wph lofdf-neg lofbeq 

    wph wn wps wn wi
    wph wn lofdf-encl wps wn lofdf-juxt
    lofdf-void lofdf-void lofdf-void
    wps lofdf-encl wph lofdf-juxt
    wph wn wps wn wi wps wph wi wi

    wph wn wps wn lofdf-imp 

    wps wph wi
    wps lofdf-encl wph lofdf-juxt
    wph wn wps wn wi lofdf-encl
    lofdf-void
    wph wn wps wn wi wps wph wi wi

    wps wph lofdf-imp

    wph wn wps wn wi wps wph wi 
    lofdf-imp
    lofreps
 
    lofrepbxs
    lofrepbxs
    lofrepbxs
    
    wph lofdf-encl lofdf-encl
    wps lofdf-encl
    lofdf-void lofdf-void lofdf-void wph
    lofc2x

    loftrans
    
    wph lofdf-void lofdf-void lofdf-void wps lofdf-encl wph lofdf-juxt
    lofc1bx

    loftrans
    
    wph lofdf-void wps lofdf-encl lofdf-void   
    lofc2e

    loftrans
    lofelim
    $.

  ${
    $( Minor premise for modus ponens. $)
    min $e |- ph $.
    $( Major premise for modus ponens. $)
    maj $e |- ( ph -> ps ) $.
    ax-mp $p |- ps $=
    wph wps
    wph lofdf-encl wps lofdf-juxt
    wph wps wi
    wph lofdf-encl wps lofdf-juxt
    lofdf-void lofdf-encl

    wph wps lofdf-imp 
    wph wps wi  maj lofintr
    lofeucr
    lofelim
    min
    lofmp
    $.
  $}

  

$(
  ----------------------------------------------------------------------------
                                 REFERENCES
  ----------------------------------------------------------------------------

  1. [Moro] Moro, Naip, "lof.mm", Metamath file (2016); available at 
     https://github.com/naipmoro/lofmm/blob/master/lof.mm .
  2. [Spencer-Brown] Spencer-Brown, George, "Laws of Form", Allen & Unwin,
     London (1969).
  3. 
$)

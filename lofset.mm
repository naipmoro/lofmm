$(
  lofset.mm    
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
                              0. Introduction
  -----------------------------------------------------------------------------

  In [Moro] I presented metamath derivations of Spencer-Brown's Primary Algebra
  (details of the algebra, which will hereafter be cited as "LoF" can be found
  in chapter 6 of [Spencer-Brown]).  [Moro] was a  stand-alone project that,
  for maximum readability, intentionally bypassed compatibility with set.mm,
  metamath's ongoing formalization of mathematics.  Here I present a version
  which is more than just compatible; I derive set.mm's propositional calculus
  from LoF.  There is nothing surprising in this -- classical propositional
  logic is one of the interpretations of LoF (Boolean algebra is another).  The
  real interest lies in the means of derivation.

  First a note about notation.  To avoid conflict with set.mm, I use grave
  accented brackets, "[`" and "`]" to represent the boundary (or "cross") of
  LoF.  This seemed to me to broadcast the least visual noise (readers may
  disagree).  Similarly I use ".=" for the equals sign.  
  
  LoF is typically presented as an equational logic (although I show that,
  technically speaking, equations can be avoided).  In other words, axioms and
  theorems are in the form P .= Q.  Transitioning from this to the 
  implicational form that traditionally characterizes classical propositional
  logic can be done in various ways.  I believe the technique chosen here is
  the simplest, relying on the single additional axiom ~ lofax-ded , the
  equational analogue of modus ponens:

  ${
    lofax-ded.1 $e |- ph $.
    lofax-ded.2 $e |- ph .= ps $.
    lofax-ded   $a |- ps $.
  $}

  With this tool in hand, and with appropriate definitions of "implies" and
  "not", I prove ~ ax-1 , ~ ax-2 , ~ ax-3 , and ~ mp as theorems of LoF.
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

  $( Empty space is a wff.   $)
  lofdf-void $a wff $.

  $( If ` ph ` is a wff, so is ` [` ph `] ` . $)
  lofdf-encl $a wff [` ph `] $.

  $( If ` ph ` and ` ps ` are wffs, so is ` ph ps ` .  This rule introduces
     technical ambiguity into the formal language and some of the more popular
     metamath parsers are unable to accomodate it.  However, since the system
     is inherently associative, this has no effect on the validity of the
     formal derivations and all proper validators will accept the results. $)
  lofdf-juxt $a wff ph ps $.

$(
  -----------------------------------------------------------------------------
                  3. The four primitive rules of formal derivation
  -----------------------------------------------------------------------------

  In [Moro] equality, represented by "=", was one of the primitive constants of
  the language.  But the symbol is superfluous, as in a Boolean system equality
  and equivalence are synonyms.  Let us interpret the form 
  ` [` [` ph `] [` ps `] `] [` ph ps `] ` to mean " ` ph ` equals (or is
  equivalent to) ` ps ` ".  All of LoF can be expressed accordingly, and I will
  call this the "unitary form" of LoF.  Below I state the four primitive rules
  of LoF derivation and a handful of associated theorems in this form, as a
  demonstration that it can be done.  What is theoretically possible is not
  always cognitively palatable, so I subsequently jettison this approach and
  return to explicit equations, what I call LoF's "normal form". 
$)

  ${
    lofax-euc.1 $e |- [` [` ph `] [` ps `] `] [` ph ps `] $.
    lofax-euc.2 $e |- [` [` ch `] [` ps `] `] [` ch ps `] $.
    $( We read this rule as:  "If ` ph ` is equal to ` ps ` and ` ch ` is equal
       to ` ps ` , then we can assert that ` ph ` is equal to ` ch ` ". $)
    lofax-euc $a |- [` [` ph `] [` ch `] `] [` ph ch `] $.
  $}

  ${
    lofax-beq.1 $e |- [` [` ph `] [` ps `] `] [` ph ps `] $.
    $( We read this rule as:  "If ` ph ` is equal to ` ps ` , then we can
       assert that ` [` ph `] ` is equal to ` [` ps `] ` ". $)
    lofax-beq $a |- [` [` [` ph `] `] [` [` ps `] `] `] [` [` ph `] [` ps `] `]
    $.
  $}

  ${
    lofax-sub.1 $e |- [` [` ph `] [` ps `] `] [` ph ps `] $.
    $( We read this rule as:  "If ` ph ` is equal to ` ps ` , then we can
       assert that ` ph ze ` is equal to ` ps ze ` ". $)
    lofax-sub $a |- [` [` ph ze `] [` ps ze `] `] [` ph ze ps ze `] $.
  $}
  
  $( We read this rule as:  " ` ph ps ` is equal to ` ps ph ` ". $)
  lofax-cmm $a |- [` [` ph ps `] [` ps ph `] `] [` ph ps ps ph `] $.

$(
  -----------------------------------------------------------------------------
                        4. Additional rules of derivation
  -----------------------------------------------------------------------------
$)

  $( We read this theorem as:  " ` ph ` is equal to ` ph ` ". $)
  lofidu $p |- [` [` ph `] [` ph `] `] [` ph ph `] $=
    wph lofdf-void lofax-cmm $.
    $( [26-Jan-2017] $)

  ${
    lofsymu.1 $e |- [` [` ph `] [` ps `] `] [` ph ps `] $.
    $( We read this theorem as:  "If ` ph ` is equal to ` ps ` , then we can
       assert that ` ps ` is equal to ` ph ` ". $)
    lofsymu $p |- [` [` ps `] [` ph `] `] [` ps ph `] $=
      wps wps wph wps lofidu lofsymu.1 lofax-euc $.
      $( [26-Jan-2017] $)
  $}

  ${
    loftransu.1 $e |- [` [` ph `] [` ps `] `] [` ph ps `] $.
    loftransu.2 $e |- [` [` ps `] [` ch `] `] [` ps ch `] $.
    $( We read this theorem as:  "If ` ph ` is equal to ` ps ` and ` ps ` is
       equal to ` ch ` , then we can assert that ` ph ` is equal to ` ch ` ".
    $)
    loftransu $p |- [` [` ph `] [` ch `] `] [` ph ch `] $=
      wph wps wch loftransu.1 wps wch loftransu.2 lofsymu lofax-euc $.
      $( [26-Jan-2017] $)
  $}

$(
  -----------------------------------------------------------------------------
                     5. Introducing the notion of equality
  -----------------------------------------------------------------------------
$)

  $c .= $. $( Equality (read:  "is equal to" or "is equivalent to") $)

  ${
    lofdf-equiv.1 $e |- ph .= ps $.
    $( Define equality in terms of LoF's unitary formalism. $)
    lofdf-equiv $a |- [` [` ph `] [` ps `] `] [` ph ps `] $.
  $}

  ${
    lofdf-uni.1 $e |- [` [` ph `] [` ps `] `] [` ph ps `] $.
    $( Translate LoF unitary form into normal form. $)
    lofdf-uni $a |- ph .= ps $.
  $}

$(
  -----------------------------------------------------------------------------
                   6. Equality theorems of formal derivation
  -----------------------------------------------------------------------------
$)

  ${
    lofeuc.1 $e |- ph .= ps $.
    lofeuc.2 $e |- ch .= ps $.
    $( Two things equal to the same thing are equal to each other.  This is
       Euclid's first Common Notion and, in an equational logic, this and its
       sibling, transitivity, are the main engine of derivation. $)
    lofeuc $p |- ph .= ch $=
      wph wch wph wps wch wph wps lofeuc.1 lofdf-equiv wch wps lofeuc.2
      lofdf-equiv lofax-euc lofdf-uni $.
      $( [26-Jan-2017] $)
  $}


  ${
    lofbeq.1 $e  |- ph .= ps $.
    $( Enclosing equal forms leaves equal forms. $)
    lofbeq $p |- [` ph `] .= [` ps `] $=
      wph lofdf-encl wps lofdf-encl wph wps wph wps lofbeq.1 lofdf-equiv
      lofax-beq lofdf-uni $.
      $( [26-Jan-2017] $)
  $}


  ${
    lofsub.1 $e |- ph .= ps $.
    $( Juxtaposing the same form with equal forms leaves equal forms. $)
    lofsub $p |- ph ze .= ps ze $=
      wph wze lofdf-juxt wps wze lofdf-juxt wph wps wze wph wps lofsub.1
      lofdf-equiv lofax-sub lofdf-uni $.
      $( [26-Jan-2017] $)
  $}

  $( Commutativity of LoF. $)
  lofcmm $p |- ph ps .= ps ph $=
    wph wps lofdf-juxt wps wph lofdf-juxt wph wps lofax-cmm lofdf-uni $.
    $( [26-Jan-2017] $)

  $( From the common notion that two
     things equal to the same thing are equal to each other and from the
     commutativity of LoF, we derive the reflexivity, symmetry, and
     transitivity of '='.  Note that such a derivation is not possible in a
     traditional formal system without additional axioms -- it is the ability
     to reference the empty (or void) form that allows it here. $)

  $( ` .= ` is reflexive. $)
  lofid $p |- ph .= ph $=
    wph lofdf-void lofcmm $.
    $( [6-Sep-2015] $)

  ${
    lofsym.1 $e |- ph .= ps $.
    $( ` .= ` is symmetric. $)
    lofsym $p |- ps .= ph $=
      wps wps wph wps lofid lofsym.1 lofeuc $.
      $( [2-Sep-2015] $)
  $}

  ${
    loftrans.1 $e |- ph .= ps $.
    loftrans.2 $e |- ps .= ch $.
    $( ` ` = ` is transitive. $)
    loftrans $p |- ph .= ch $=
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
    lofeucr.1 $e |- ph .= ps $.
    lofeucr.2 $e |- ph .= ch $.
    $( A commuted - or reversed - version of ~ lofeuc. $)
    lofeucr $p |- ps .= ch $=
      wps wph wch wph wps lofeucr.1 lofsym lofeucr.2 loftrans $.
      $( [2-Sep-2015] $)
  $}

  ${
    lofsubr.1 $e |- ph .= ps $.
    $( A commuted version of lofsub. $)
    lofsubr $p |- et ph .= et ps $=
      wps wet lofdf-juxt wet wph lofdf-juxt wet wps lofdf-juxt wph wet
      lofdf-juxt wps wet lofdf-juxt wet wph lofdf-juxt wph wps wet lofsubr.1
      lofsub wph wet lofcmm lofeucr wps wet lofcmm lofeucr $.
      $( [2-Sep-2015] $)
  $}

  $( More versions of the substitution principle. Our lack of access to the
     implicit commutativity of 2D forces us to spell out each case. $)
  ${
    lofsubst.1 $e |- ph .= ps $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    lofsubst $p |- et ph ze .= et ps ze $=
      wph wze lofdf-juxt wps wze lofdf-juxt wet wph wps wze lofsubst.1 lofsub
      lofsubr $.
      
    $( [2-Sep-2015] $)
    lofsubstr $p |- et ph ze .= ze ps et $=
      wet wph lofdf-juxt wze lofdf-juxt wet wze lofdf-juxt wps lofdf-juxt wze
      wps lofdf-juxt wet lofdf-juxt wph wze lofdf-juxt wze wps lofdf-juxt wet
      wph wze lofdf-juxt wps wze lofdf-juxt wze wps lofdf-juxt wph wps wze
      lofsubst.1 lofsub wps wze lofcmm loftrans lofsubr wet wze wps lofdf-juxt
      lofcmm loftrans $.
      
    $( [2-Sep-2015] $)
    lofsubb1 $p |- si [` et ph ze `] rh .= si [` et ps ze `] rh $=
      wet wph lofdf-juxt wze lofdf-juxt lofdf-encl wet wps lofdf-juxt wze
      lofdf-juxt lofdf-encl wsi wrh wet wph lofdf-juxt wze lofdf-juxt wet wps
      lofdf-juxt wze lofdf-juxt wph wps wet wze lofsubst.1 lofsubst lofbeq
      lofsubst $.
      
    $( [2-Sep-2015] $)
    lofsubb2 $p |- si [` et ph ze `] rh .= si [` ze ps et `] rh $=
      wet wph lofdf-juxt wze lofdf-juxt lofdf-encl wze wps lofdf-juxt wet
      lofdf-juxt lofdf-encl wsi wrh wet wph lofdf-juxt wze lofdf-juxt wze wps
      lofdf-juxt wet lofdf-juxt wph wps wet wze lofsubst.1 lofsubstr lofbeq
      lofsubst $.
      $( [2-Sep-2015] $)
  $}

  ${
    lofrep.1 $e |- ph .= ps $.
    lofrep.2 $e |- et ph ze .= mu $.
    $( Direct substitution into an equation. $)
    lofrep $p |- et ps ze .= mu $=
      wet wph lofdf-juxt wze lofdf-juxt wet wps lofdf-juxt wze lofdf-juxt wmu
      wph wps wet wze lofrep.1 lofsubst lofrep.2 lofeucr $.
      $( [18-Sep-2015] $)
  $}

  ${
    lofreps.1 $e |- ph .= ps $.
    lofreps.2 $e |- mu .= et ph ze $.
    $( Direct substitution into a switched equation. $)
    lofreps $p |- mu .= et ps ze $=

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
    lofrepbx.1 $e |- ph .= ps $.
    lofrepbx.2 $e |- si [` et ph ze `] rh .= mu $.
    $( Direct substitution into a bounded-form equation. $)
    lofrepbx $p |- si [` et ps ze `] rh .= mu $=
      wsi wet wph lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt wrh
      lofdf-juxt wsi wet wps lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt
      wrh lofdf-juxt wmu wph wps wet wze wsi wrh lofrepbx.1 lofsubb1 lofrepbx.2
      lofeucr $.
      $( [18-Sep-2015] $)
  $}

  ${
    lofrepbxs.1 $e |- ph .= ps $.
    lofrepbxs.2 $e |- mu .= si [` et ph ze `] rh $.
    $( Direct substitution into a switched bounded-form equation. $)
    lofrepbxs $p |- mu .= si [` et ps ze `] rh $=
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
    lofrepbd.1  $e |- ph .= ps $.
    lofrepbd.2  $e |- [` [` et ph ze `] `] .= mu $.
    $( Direct substitution into a double bounded-form equation. $)
    lofrepbd    $p |- [` [` et ps ze `] `] .= mu $=
      ( lofdf-juxt lofdf-encl lofdf-void lofsubb1 lofbeq lofeucr ) CAHDHIZICBHD
      HIZIENOABCDJJFKLGM $.
      $( [3-Oct-2015] $)
  $}
  

  ${
    lofquad.1 $e |- ph .= ps $.
    lofquad.2 $e |- ch .= th $.
    $( Double substitution of equivalent forms. $)
    lofquad $p |- ph ch .= ps th $=
      wph wch lofdf-juxt wps wch lofdf-juxt wps wth lofdf-juxt wph wps
      lofdf-void wch lofquad.1 lofsubst wch wth wps lofdf-void lofquad.2
      lofsubst loftrans $.
      $( [2-Sep-2015] $)
  $}

  ${
    lofins.1 $e |- ph ps .= ch th $.
    $( Insert the same form into two equivalent forms. $)
    lofins $p |- ph ze ps .= ch ze th $=
      wph wze lofdf-juxt wps lofdf-juxt wze wch lofdf-juxt wth lofdf-juxt wch
      wze lofdf-juxt wth lofdf-juxt wph wze lofdf-juxt wps lofdf-juxt wze wph
      lofdf-juxt wps lofdf-juxt wze wch lofdf-juxt wth lofdf-juxt wph wze
      lofdf-juxt wze wph lofdf-juxt wps wph wze lofcmm lofsub wph wps
      lofdf-juxt wch wth lofdf-juxt wze lofins.1 lofsubr loftrans wze wch
      lofdf-juxt wch wze lofdf-juxt wth wze wch lofcmm lofsub loftrans $.
      $( [3-Sep-2015] $)
  $}

  $( Extended commutativity. $)
  lofcmmx $p  |- et ph ze ps si .= et ps ze ph si $=
    wph wze lofdf-juxt wps lofdf-juxt wps wze lofdf-juxt wph lofdf-juxt wet wsi
    wph wps wps wph wze wph wps lofcmm lofins lofsubst $.
    $( [3-Sep-2015] $)

  $( Bounded and extended commutativity. $)
  lofcmmbx $p |- rh [` et ph ze ps si `] mu .= rh [` et ps ze ph si `] mu $=
    wph wze lofdf-juxt wps lofdf-juxt wps wze lofdf-juxt wph lofdf-juxt wet wsi
    wrh wmu wze wze wph wps wze lofid lofsubstr lofsubb1 $.
    $( [2-Sep-2015] $)

  ${
    lofquadbx.1 $e |- ph .= ps $.
    lofquadbx.2 $e |- ch .= th $.
    $( Double substitution into a bounded and extended form. $)
    lofquadbx $p |- rh [` et ph ze ch si `] mu .= rh [` et ps ze th si `] mu $=
      wph wze lofdf-juxt wch lofdf-juxt wps wze lofdf-juxt wth lofdf-juxt wet
      wsi wrh wmu wph wch wps wth wze wph wps wch wth lofquadbx.1 lofquadbx.2
      lofquad lofins lofsubb1 $.
      $( [3-Sep-2015] $)
  $}

$(
  -----------------------------------------------------------------------------
                                 7. Axioms of LoF
  -----------------------------------------------------------------------------
$)

  $( Position. $)
  lofj1 $a |- [` [` ph `] ph `] .= $.

  $( Transposition. $)
  lofj2 $a |- [` [` ph ch `] [` ps ch `] `] .= [` [` ph `] [` ps `] `] ch $.

$(
  -----------------------------------------------------------------------------
                                8. Theorems of LoF
  -----------------------------------------------------------------------------
$)

  $( Reflexion. $)
  lofc1 $p |- [` [` ph `] `] .= ph $=
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
    wph lofdf-encl lofj1 lofsub lofsym wph lofdf-encl wph wph lofdf-encl
    lofdf-encl lofj2 lofeuc wph lofdf-encl wph lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl wph lofdf-encl lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl
    lofdf-void wph wph lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-void
    lofdf-void wph lofdf-encl wph lofdf-encl lofdf-encl lofdf-void lofdf-void
    lofdf-void lofdf-void lofdf-void lofcmmbx lofsubb1 loftrans wph lofdf-encl
    lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl lofdf-void lofdf-void wph
    wph lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-void lofdf-void wph
    lofdf-encl lofj1 lofsubb1 loftrans wph wph lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl wph lofdf-encl lofdf-encl wph lofdf-juxt lofdf-encl lofdf-void
    wph lofdf-encl wph lofdf-juxt lofdf-encl lofdf-void lofdf-void lofdf-void
    lofdf-void lofdf-void wph wph lofdf-encl lofdf-encl lofdf-void lofdf-void
    lofdf-void lofdf-void lofdf-void lofcmmbx wph lofdf-encl wph lofdf-juxt
    lofdf-encl lofdf-void wph lofj1 lofsym lofquadbx loftrans wph lofdf-encl
    lofdf-encl wph lofdf-juxt lofdf-encl wph lofdf-encl wph lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl lofdf-encl wph
    lofdf-encl lofdf-encl lofdf-juxt lofdf-encl wph lofdf-juxt wph wph
    lofdf-encl lofdf-encl wph lofdf-encl wph lofj2 wph lofdf-encl lofdf-encl
    lofdf-encl wph lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-void wph
    wph lofdf-encl lofdf-encl lofj1 lofsub loftrans loftrans $.
    $( [6-Sep-2015] $)

  $( Generation. $)
  lofc2 $p |- [` ph ps `] ps .= [` ph `] ps $=
    wph lofdf-encl wps lofdf-juxt lofdf-encl wps lofdf-encl wps lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl wph wps lofdf-juxt lofdf-encl wps
    lofdf-juxt wph lofdf-encl wps lofdf-juxt wph lofdf-encl wps lofdf-juxt
    lofdf-encl wps lofdf-encl wps lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-encl lofdf-encl wps lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    wps lofdf-juxt wph wps lofdf-juxt lofdf-encl wps lofdf-juxt wph lofdf-encl
    wps lofdf-encl wps lofj2 wph lofdf-encl lofdf-encl wph wps lofdf-encl
    lofdf-encl wps lofdf-void lofdf-void lofdf-void lofdf-void wps wph lofc1 wps
    lofc1 lofquadbx loftrans wph lofdf-encl wps lofdf-juxt lofdf-encl wps
    lofdf-encl wps lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl
    wps lofdf-juxt lofdf-encl lofdf-encl wph lofdf-encl wps lofdf-juxt wps
    lofdf-encl wps lofdf-juxt lofdf-encl lofdf-void wph lofdf-encl wps
    lofdf-juxt lofdf-encl lofdf-void lofdf-void lofdf-void wps lofj1 lofsubb1
    wph lofdf-encl wps lofdf-juxt lofc1 loftrans lofeucr $.
    $( [6-Sep-2015] $)

  $( Integration. $)
  lofc3 $p |- [` `] ph .= [` `] $=
    wph lofdf-encl wph lofdf-juxt lofdf-void lofdf-encl wph lofdf-juxt
    lofdf-void lofdf-encl lofdf-void wph lofc2 wph lofdf-encl wph lofdf-juxt
    lofdf-encl lofdf-encl wph lofdf-encl wph lofdf-juxt lofdf-void lofdf-encl
    wph lofdf-encl wph lofdf-juxt lofc1 wph lofdf-encl wph lofdf-juxt lofdf-encl
    lofdf-void wph lofj1 lofbeq lofeucr lofeucr $.
    $( [6-Sep-2015] $)

  $( Iteration. $)
  lofc5 $p |- ph ph .= ph $=
    wph lofdf-encl wph lofdf-juxt lofdf-encl wph lofdf-juxt wph wph lofdf-juxt
    wph wph lofdf-encl wph lofdf-juxt lofdf-encl wph lofdf-juxt wph lofdf-encl
    lofdf-encl wph lofdf-juxt wph wph lofdf-juxt wph lofdf-encl wph lofc2 wph
    lofdf-encl lofdf-encl wph lofdf-void wph wph lofc1 lofsubst loftrans wph
    lofdf-encl wph lofdf-juxt lofdf-encl lofdf-void lofdf-void wph wph lofj1
    lofsubst lofeucr $.
    $( [6-Sep-2015] $)

  $( Occultation. $)
  lofc4 $p |- [` [` ph `] ps `] ph .= ph $=
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
    lofdf-juxt lofdf-encl wph lofdf-juxt wph wps lofdf-encl wph lofj2 wps
    lofdf-encl lofdf-encl wps wph lofdf-encl lofdf-void lofdf-void wph wps lofc1
    lofsubb1 loftrans wph wph lofdf-juxt lofdf-encl wph lofdf-encl lofdf-void
    wps lofdf-encl wph lofdf-juxt lofdf-encl lofdf-void lofdf-void wph wph
    lofdf-juxt wph lofdf-void lofdf-void lofdf-void lofdf-void wph lofc5
    lofsubb1 lofsubb1 lofeucr lofdf-void wps lofdf-encl wph lofj2 loftrans
    lofdf-void lofdf-encl wps lofdf-encl lofdf-encl lofdf-juxt lofdf-void
    lofdf-encl lofdf-void lofdf-void lofdf-void wph wps lofdf-encl lofdf-encl
    lofc3 lofsubb1 loftrans lofdf-void lofdf-encl lofdf-encl lofdf-void
    lofdf-void wph lofdf-void lofc1 lofsubst loftrans $.
    $( [6-Sep-2015] $)

  $( Corollary of c4 $)
  lofc4cor $p |- [` ph ps `] [` ph `] .= [` ph `] $=
    wph lofdf-encl lofdf-encl wps lofdf-juxt lofdf-encl wph lofdf-encl
    lofdf-juxt wph wps lofdf-juxt lofdf-encl wph lofdf-encl lofdf-juxt wph
    lofdf-encl wph lofdf-encl lofdf-encl wph lofdf-void wps lofdf-void wph
    lofdf-encl wph lofc1 lofsubb1 wph lofdf-encl wps lofc4 lofeucr $.
    $( [18-Sep-2015] $)

  $( Extension. $)
  lofc6 $p |- [` [` ph `] [` ps `] `] [` [` ph `] ps `] .= ph $=
    wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl lofdf-encl wph wph
    lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-encl wph lofdf-encl wps
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl
    lofdf-juxt wph lofdf-encl lofdf-encl wph lofdf-encl wps lofdf-encl
    lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl lofdf-juxt
    lofc1 wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
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
    lofdf-encl wps wph lofdf-encl lofj2 loftrans lofbeq wps lofdf-encl
    lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-void lofdf-void wph
    lofdf-encl lofdf-void lofdf-void wps lofdf-encl lofj1 lofsubb1 loftrans
    lofeucr wph lofc1 loftrans $.
    $( [6-Sep-2015] $)

  $( Corollary of c6 $)
  lofc6cor $p |- [` [` ph `] ps `] [` ph ps `] .= [` ps `] $=
    wps wph lofdf-juxt wph wps lofdf-juxt lofdf-void lofdf-void wph lofdf-encl
    wps lofdf-juxt lofdf-encl lofdf-void wps lofdf-encl wps wph lofcmm wps wph
    lofdf-encl lofdf-juxt wph lofdf-encl wps lofdf-juxt lofdf-void lofdf-void
    lofdf-void wps wph lofdf-juxt lofdf-encl wps lofdf-encl wps wph lofdf-encl
    lofcmm wps lofdf-encl lofdf-encl wps lofdf-void wph wps wph lofdf-encl
    lofdf-juxt lofdf-encl lofdf-void wps lofdf-encl wps lofc1 wps lofdf-encl
    lofdf-encl wps lofdf-void wph lofdf-encl lofdf-void wps lofdf-encl
    lofdf-encl wph lofdf-juxt lofdf-encl wps lofdf-encl wps lofc1 wps lofdf-encl
    wph lofc6 lofrepbx lofrepbx lofrepbx lofrepbx $.

  $( Echelon. $)
  lofc7 $p |- [` [` [` ph `] ps `] ch `] .= [` ph ch `] [` [` ps `] ch `] $=
    wph wch lofdf-juxt lofdf-encl wps lofdf-encl wch lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl
    wch lofdf-juxt lofdf-encl wph wch lofdf-juxt lofdf-encl wps lofdf-encl wch
    lofdf-juxt lofdf-encl lofdf-juxt wph wch lofdf-juxt lofdf-encl wps
    lofdf-encl wch lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-encl wph
    lofdf-encl wps lofdf-encl lofdf-encl lofdf-juxt lofdf-encl wch lofdf-juxt
    lofdf-encl wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt
    lofdf-encl wph wch lofdf-juxt lofdf-encl wps lofdf-encl wch lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl wch lofdf-juxt wph wps lofdf-encl wch lofj2 lofbeq wph
    lofdf-encl wps lofdf-encl lofdf-encl lofdf-juxt lofdf-encl wch lofdf-juxt
    wph lofdf-encl wps lofdf-juxt lofdf-encl wch lofdf-juxt wps lofdf-encl
    lofdf-encl wps wph lofdf-encl lofdf-void lofdf-void wch wps lofc1 lofsubb1
    lofbeq loftrans wph wch lofdf-juxt lofdf-encl wps lofdf-encl wch lofdf-juxt
    lofdf-encl lofdf-juxt lofc1 lofeucr $.
    $( [6-Sep-2015] $)

  $( Modified transposition. $)
  lofc8 $p |- [` [` ph `] [` ps th `] [` ch th `] `] 
             .= [` [` ph `] [` ps `] [` ch `] `] [` [` ph `] [` th `] `] $=
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
    lofdf-juxt lofdf-encl lofdf-juxt lofc1 wps wth lofdf-juxt lofdf-encl wch wth
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-encl wps lofdf-encl wch
    lofdf-encl lofdf-juxt lofdf-encl wth lofdf-juxt lofdf-encl wph lofdf-encl
    lofdf-void lofdf-void lofdf-void wps wth lofdf-juxt lofdf-encl wch wth
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wch lofdf-encl
    lofdf-juxt lofdf-encl wth lofdf-juxt wps wch wth lofj2 lofbeq lofsubb2
    lofrepbx wps lofdf-encl wch lofdf-encl lofdf-juxt lofdf-encl wth lofdf-juxt
    lofdf-encl wph lofdf-encl lofdf-juxt lofdf-encl wps lofdf-encl wch
    lofdf-encl lofdf-juxt wph lofdf-encl lofdf-juxt lofdf-encl wth lofdf-encl
    wph lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps
    lofdf-encl lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl
    wth lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt wps lofdf-encl wch
    lofdf-encl lofdf-juxt wth wph lofdf-encl lofc7 wps lofdf-encl wch lofdf-encl
    lofdf-juxt wph lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wps
    lofdf-encl lofdf-juxt wch lofdf-encl lofdf-juxt lofdf-encl wth lofdf-encl
    wph lofdf-encl lofdf-juxt lofdf-encl wph lofdf-encl wth lofdf-encl
    lofdf-juxt lofdf-encl wps lofdf-encl wch lofdf-encl lofdf-juxt wph
    lofdf-encl lofdf-void lofdf-void lofdf-void lofdf-void lofdf-void lofcmmbx
    wth lofdf-encl wph lofdf-encl lofdf-void lofdf-void lofdf-void lofdf-void
    lofdf-void lofcmmbx lofquad loftrans loftrans $.
    $( [6-Sep-2015] $)

  $( Crosstransposition. $)
  lofc9 $p |- [` [` [` ps `] [` ph `] `] [` [` ch `] [` ph `] `]
             [` [` th `] ph `] [` [` ta `] ph `] `]
             .= [` [` ph `] ps ch `] [` ph th ta `] $=
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
    lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt lofc1 wth lofdf-encl wph
    lofdf-juxt lofdf-encl wta lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl wth wta lofdf-juxt lofdf-encl wph lofdf-juxt wth lofdf-encl wph
    lofdf-juxt lofdf-encl wta lofdf-encl wph lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl wth lofdf-encl lofdf-encl wta lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl wph lofdf-juxt wth wta lofdf-juxt lofdf-encl wph lofdf-juxt wth
    lofdf-encl wta lofdf-encl wph lofj2 wth lofdf-encl lofdf-encl wth wta
    lofdf-encl lofdf-encl wta lofdf-void lofdf-void lofdf-void lofdf-void wph
    wth lofc1 wta lofc1 lofquadbx loftrans lofbeq lofeucr lofsubb2 wth wta
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
    lofdf-juxt wps lofdf-encl wch lofdf-encl wph lofdf-encl lofc8 wps lofdf-encl
    lofdf-encl wps wch lofdf-encl lofdf-encl wch wth wta lofdf-juxt lofdf-encl
    wph lofdf-juxt lofdf-encl lofdf-void lofdf-void lofdf-void wth wta
    lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl wph lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl wps lofc1 wch lofc1 lofquadbx loftrans wph lofdf-encl
    lofdf-encl wph wth wta lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl
    lofdf-void wth wta lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl wps
    lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-void wph lofc1 lofsubb1 loftrans
    wth wta lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl wph lofdf-juxt wth
    wta lofdf-juxt lofdf-encl lofdf-encl wph lofdf-juxt lofdf-void lofdf-void
    wth wta lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl wps lofdf-juxt wch
    lofdf-juxt lofdf-encl lofdf-void wth wta lofdf-juxt lofdf-encl wph lofc2
    lofsubb1 loftrans wth wta lofdf-juxt lofdf-encl lofdf-encl wth wta
    lofdf-juxt lofdf-void wph wth wta lofdf-juxt lofdf-encl wph lofdf-juxt
    lofdf-encl wps lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-void wth wta
    lofdf-juxt lofc1 lofsubb1 loftrans wth wta lofdf-juxt lofdf-encl wph
    lofdf-juxt lofdf-encl wps lofdf-juxt wch lofdf-juxt wth wta lofdf-juxt wph
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl wth wta lofdf-juxt wph
    lofdf-juxt lofdf-encl lofdf-juxt wth wta lofdf-juxt lofdf-encl wph
    lofdf-juxt lofdf-encl wps lofdf-juxt wch lofdf-juxt lofdf-encl wth wta
    lofdf-juxt wph lofdf-juxt lofdf-encl lofdf-juxt wph lofdf-encl wps
    lofdf-juxt wch lofdf-juxt lofdf-encl wph wth lofdf-juxt wta lofdf-juxt
    lofdf-encl lofdf-juxt wth wta lofdf-juxt lofdf-encl wph lofdf-juxt
    lofdf-encl wps lofdf-juxt wch lofdf-juxt wth wta lofdf-juxt wph lofdf-juxt
    lofdf-encl lofc2 wth wta lofdf-juxt lofdf-encl wph lofdf-juxt lofdf-encl wps
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
    lofdf-juxt lofdf-encl lofdf-void wps wch lofdf-juxt wph lofc1 lofsubb1 wph
    lofdf-encl lofdf-encl wph lofdf-void wth wta lofdf-juxt lofdf-void
    lofdf-void wph lofc1 lofsubb1 lofquadbx wph lofdf-encl lofdf-encl wth wta
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
    lofdf-juxt lofdf-encl wph lofdf-encl wth wta lofdf-juxt lofc6 lofsubb1 wth
    wta lofdf-juxt wph lofdf-void lofdf-void lofdf-void wph lofdf-encl wps
    lofdf-juxt wch lofdf-juxt lofdf-encl lofdf-void lofcmmbx loftrans loftrans
    lofeucr loftrans lofeucr loftrans loftrans $.
    $( [6-Sep-2015] $)

  $( Intial I1. $)
  lofi1 $p |- [` `] [` `] .= [` `]  $=
    lofdf-void lofdf-encl lofc5
    $.

  $( Intial I2. $)
  lofi2 $p |- [` [` `] `] .= $=
    lofdf-void lofj1
    $.

$(
  -----------------------------------------------------------------------------
                      9. Generalizations of LoF consequences
  -----------------------------------------------------------------------------
$)
 
  $( Versions of C1. $)

  lofc1r $p |- ph .= [` [` ph `] `] $=
    wph lofdf-encl lofdf-encl  wph
    wph lofc1 lofsym  $.

  lofc1x $p |- et [` [` ph `] `] ze .= et ph ze $=
    wph lofdf-encl lofdf-encl  wph
    wet wze
    wph lofc1 
    lofsubst  $.

  lofc1rx $p |-  et ph ze .=  et [` [` ph `] `] ze  $=
    wph  wph lofdf-encl lofdf-encl
    wet wze
    wph lofc1r
    lofsubst   $.

  lofc1bx $p |- si [` et [` [` ph `] `] ze `] rh .= si [` et ph ze `] rh $=
    wet wph lofdf-encl lofdf-encl lofdf-juxt wze lofdf-juxt
    wet wph lofdf-juxt wze lofdf-juxt
    lofdf-void lofdf-void
    wsi wrh
    wph wet wze lofc1x
    lofsubb1  $.

  lofc1rbx $p |- si [` et ph ze `] rh .=  si [` et [` [` ph `] `] ze `] rh  $=
    wsi wet wph lofdf-encl lofdf-encl lofdf-juxt wze lofdf-juxt lofdf-encl
    lofdf-juxt wrh lofdf-juxt
    wsi wet wph lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt wrh lofdf-juxt
    wph wet wze wsi wrh  lofc1bx lofsym  $.
  
  $( Versions of C2. $)
  lofc2x $p |- et [` ph ps ze `] si ps rh .= et [` ph ze `] si ps rh $= 

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
    lofc2

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

  lofc2bx $p |- mu [` et [` ph ps ze `] si ps rh `] la
                .= mu [` et [` ph ze `] si ps rh `] la $=
    wet wph wps lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt
    wsi lofdf-juxt wps lofdf-juxt wrh lofdf-juxt
    wet wph wze lofdf-juxt lofdf-encl lofdf-juxt
    wsi lofdf-juxt wps lofdf-juxt wrh lofdf-juxt
    lofdf-void lofdf-void wmu wla
    wph wps wet wze wsi wrh
    lofc2x
    lofsubb1 $.

  lofc2rx $p |-  et ps ze [` ph ps si `] rh .= et ps ze [` ph si `] rh $=
       
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

  lofc2rbx $p |- mu [` et [` ph ze `] si ps rh `] la
                 .= mu [` et [` ph ps ze `] si ps rh `] la $=
    wmu wet wph wps lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt
    wsi lofdf-juxt wps lofdf-juxt wrh lofdf-juxt lofdf-encl lofdf-juxt
    wla lofdf-juxt
    wmu wet wph wze lofdf-juxt lofdf-encl lofdf-juxt
    wsi lofdf-juxt wps lofdf-juxt wrh lofdf-juxt lofdf-encl lofdf-juxt
    wla lofdf-juxt
    wph wps wet wze wsi wrh wmu wla
    lofc2bx
    lofsym $.

  lofc2e $p |-  et [` ph `] ze ph si .=  [` `]  $=

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
    lofc3
    loftrans
    loftrans
    $.
  
  $( Versions of C3. $)
  lofc3x $p |- ph [` `] ps .= [` `]  $= 
    wph lofdf-void lofdf-encl lofdf-juxt wps lofdf-juxt
    lofdf-void lofdf-encl wps lofdf-juxt wph lofdf-juxt
    lofdf-void lofdf-encl

    wph lofdf-void lofdf-encl wps lofdf-juxt lofcmm 
    wps wph lofdf-juxt lofc3

    loftrans
    $.

  lofc3bx $p |- et [` ph [` `] ps `] ze .= et ze  $=
    
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
  lofc4x $p |- si [` et [` ph `] ze `] rh ph mu .= si ph rh mu $=

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

    wph wet wze lofdf-juxt lofc4

    wsi wph lofdf-encl wet lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt
    wph lofdf-juxt wrh lofdf-juxt wmu lofdf-juxt
    lofid

    lofrep
    lofeuc
    $.

  lofc4rx $p |- si ph rh mu .= si [` et [` ph `] ze `] rh ph mu $=
    wsi wet wph lofdf-encl lofdf-juxt wze lofdf-juxt lofdf-encl lofdf-juxt
    wrh lofdf-juxt wph lofdf-juxt wmu lofdf-juxt
    wsi wph lofdf-juxt wrh lofdf-juxt wmu lofdf-juxt
    wph wet wze wsi wrh wmu
    lofc4x
    lofsym
    $.

  $( Versions of C5. $)
  lofc5x $p |- et ph ze ph si .= et ph ze si  $=
                
    wet wph lofdf-juxt wze lofdf-juxt wph lofdf-juxt wsi lofdf-juxt
    wet wph lofdf-juxt wph lofdf-juxt wze lofdf-juxt wsi lofdf-juxt
    wet wph lofdf-juxt wze lofdf-juxt wsi lofdf-juxt

    wze wph wet wph lofdf-juxt lofdf-void wsi
    lofcmmx

    wph wph lofdf-juxt   wph
    wet   wze wsi lofdf-juxt
    wet wph lofdf-juxt wph lofdf-juxt wze lofdf-juxt wsi lofdf-juxt
    wph lofc5
    wet wph lofdf-juxt wph lofdf-juxt wze lofdf-juxt wsi lofdf-juxt
    lofid
    lofrep
    lofeuc
    $.

  lofc5rx $p |- et ph ze si .= et ph ze ph si $=
    wet wph lofdf-juxt wze lofdf-juxt wph lofdf-juxt wsi lofdf-juxt
    wet wph lofdf-juxt wze lofdf-juxt wsi lofdf-juxt
    wph wet wze wsi  lofc5x
    lofsym
    $.

  $( Versions of J1. $)
  lofj1x $p |-   rh [` et [` ph `] ze ph si `] mu .= rh mu $=
                 
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

  lofj1rx $p |- rh mu .= rh [` et [` ph `] ze ph si `] mu $=
    wrh wet wph lofdf-encl lofdf-juxt wze lofdf-juxt wph lofdf-juxt
    wsi lofdf-juxt lofdf-encl lofdf-juxt wmu lofdf-juxt
    wrh wmu lofdf-juxt
    wph wet wze wsi wrh wmu 
    lofj1x
    lofsym
    $.

  $( Versions of J2. $)
  lofj2x $p |- et [` [` ph ch `] [` ps ch `] `] ze si
               .= et [` [` ph `] [` ps `] `] ze ch si $=    

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
    lofj2
    lofsubst
    
    wch wze
    wet wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-void
    wsi
    lofcmmx
    loftrans
    $.

  lofj2rx $p |- et [` [` ph `] [` ps `] `] ze ch si
                .= et [` [` ph ch `] [` ps ch `] `] ze si $=
    
    wet wph wch lofdf-juxt lofdf-encl wps wch lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt wze lofdf-juxt wsi lofdf-juxt
    wet wph lofdf-encl wps lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    wze lofdf-juxt wch lofdf-juxt wsi lofdf-juxt
    
    wph wps wch wet wze wsi
    lofj2x
    lofsym
    $.

$(
  -----------------------------------------------------------------------------
                        10. Implementing LoF deduction
  -----------------------------------------------------------------------------
$)  

  $( ---------------- MIXED THEOREMS ----------------- $)
  lofelimeq $p |- [` [` ph `] [` [` `] `] `] [` ph [` `] `] .= ph $=
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
    lofdf-void lofdf-encl lofdf-juxt lofdf-encl lofi2 lofsubb1 wph lofdf-encl
    lofdf-encl wph lofdf-void wph lofdf-void lofdf-encl lofdf-juxt lofdf-encl
    wph lofc1 lofsubst loftrans wph lofdf-void lofdf-encl lofdf-void lofdf-void
    lofdf-void wph lofdf-void lofcmmbx loftrans wph lofdf-void lofdf-encl wph
    lofdf-juxt lofdf-encl lofcmm loftrans lofdf-void lofdf-encl wph lofc2
    loftrans lofdf-void lofdf-encl lofdf-encl lofdf-void lofdf-void wph lofi2
    lofsubst loftrans $.
    $( [29-Jan-2017] $)


  $( The LoF deduction axiom. $)
  ${
    lofax-ded.1 $e |- ph $.
    lofax-ded.2 $e |- ph .= ps $.
    $( If we assert both ` ph ` and that ` ph ` is equal to ` ps ` , we can
       assert ` ps ` . $)
    lofax-ded   $a |- ps $.
  $}

  $( Truth equivalence elimination.  $)
  ${
    lofelim.1 $e |- ph .= [` `] $.
    $( If ` ph ` is equivalent to True, we can assert ` ph ` . $)
    lofelim   $p |- ph $=
    
    wph lofdf-encl lofdf-void lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-void lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    wph

    wph lofdf-void lofdf-encl
    lofelim.1
    lofdf-equiv

    wph lofelimeq
    
    
    
    lofax-ded
    $.
  $}

  $( Truth equivalence introduction.  $)
  ${
    lofintr.1 $e |- ph $.
    $( If we can assert ` ph ` , then we can assert that ` ph ` is
       equivalent to True. $)
    lofintr   $p |- ph .= [` `]  $=
    wph lofdf-void lofdf-encl
    wph
    wph lofdf-encl lofdf-void lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-void lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt

    lofintr.1

    wph lofdf-encl lofdf-void lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    wph lofdf-void lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    wph
    
    wph lofelimeq lofsym
    
    lofax-ded
    lofdf-uni
    $.
  $}

  ${
    lofeucrelim.1 $e |- ph .= ps $.
    lofeucrelim.2 $e |- ph .= [` `] $.
    lofeucrelim   $p |- ps $=
      wps
      wph wps lofdf-void lofdf-encl
      lofeucrelim.1 lofeucrelim.2 lofeucr
      lofelim
    $.
  $}

  ${
    loftranselim.1 $e |- ph .= ps $.
    loftranselim.2 $e |- ps .= [` `] $.
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
    lofand   $p |- [` [` ph `] [` ps `] `] $=

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
    lofdf-equiv
    lofintr
    lofrepbx
    
    lofeucr
    lofelim
    $.
  $}

  

  ${   
    lofmp.1 $e |- ph $.
    lofmp.2 $e |- [` ph `] ps $.
    lofmp   $p |- ps  $=

    wps
    wph lofdf-encl
    lofdf-void
    lofdf-void
    wps
    lofdf-void lofdf-encl
    
    wph lofdf-encl    lofdf-void lofdf-encl lofdf-encl    lofdf-void
    wph lofdf-void lofdf-encl wph lofmp.1 lofintr lofbeq
    lofdf-void lofc1
    loftrans
    
    wph lofdf-encl wps lofdf-juxt  lofmp.2 lofintr

    lofrep
    lofelim
    $.
  $}  

$(
  -----------------------------------------------------------------------------
                   11. Defining classical propositional logic
  -----------------------------------------------------------------------------
$)

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
  lofdf-imp $a |- ( ph -> ps ) .= [` ph `] ps $.


  $( Define classical negation in terms of LoF. $)
  lofdf-neg $a |- -. ph .= [` ph `] $.

$(
  -----------------------------------------------------------------------------
                 12. Propositional logic is superfluous (an example)
  -----------------------------------------------------------------------------
$)

  lofpm2.18 $p |-  ( ( -. ph -> ph ) -> ph ) $=
    wph wn wph wi wph wi

    wph wn wph wi wph wi
    wph lofdf-encl wph lofdf-juxt
    lofdf-void lofdf-encl

    wph wn
    wph lofdf-encl
    lofdf-void
    wph
    wph wn wph wi wph wi
    
    wph lofdf-neg

    wph wn wph wi wph wi
    wph wn lofdf-encl wph lofdf-juxt lofdf-encl wph lofdf-juxt
    wph wn wph lofdf-juxt
                 
    wph wn wph wi
    wph wn lofdf-encl wph lofdf-juxt
    lofdf-void lofdf-void lofdf-void wph
    wph wn wph wi wph wi
    wph wn wph  lofdf-imp              
    wph wn wph wi wph               
    lofdf-imp
    lofrepbxs
   
    wph wn lofdf-encl wph lofdf-juxt lofdf-encl wph lofdf-juxt
    wph wn lofdf-encl lofdf-encl wph lofdf-juxt
    wph wn wph lofdf-juxt
    
    wph wn lofdf-encl
    wph
    lofdf-void  lofdf-void lofdf-void lofdf-void
    lofc2x
    
    wph wn  lofdf-void wph  lofc1x
    loftrans
    loftrans
    lofreps

    wph lofdf-void lofdf-void lofdf-void  lofc2e
    loftrans
    lofelim
    $.

$(
  -----------------------------------------------------------------------------
                  12. Proving the axioms of propositional logic
  -----------------------------------------------------------------------------
$)

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
    min
    wph lofdf-encl wps lofdf-juxt
    wph wps wi
    wph lofdf-encl wps lofdf-juxt
    lofdf-void lofdf-encl

    wph wps lofdf-imp 
    wph wps wi  maj lofintr
    lofeucr
    lofelim
    
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

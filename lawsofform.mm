$(
  lawsofform.mm    version 0.1.0    Copyright (C) 2017 naipmoro
  This file is made available under the MIT License:
  http://opensource.org/licenses/MIT

  lof.mm presents metamath derivations of the Primary Algebra from
  Spencer-Brown, G. (1969) Laws of Form (Allen & Unwin, London),
  hereafter cited as LoF.
$)

  $( constants $)
  $c `[ `] |- loff $.

  $( variables $)
  $v p q r s t u v w x y z $.

  $( forms $)
  lfp $f loff p $.
  lfq $f loff q $.
  lfr $f loff r $.
  lfs $f loff s $.
  lft $f loff t $.
  lfu $f loff u $.
  lfv $f loff v $.
  lfw $f loff w $.
  lfx $f loff x $.
  lfy $f loff y $.
  lfz $f loff z $.

  $( Axioms ---------------------------------------------------
     In keeping with the spirit of LoF's austerity, I aimed for the most
     minimal formalism possible. I start with the five constant symbols listed
     above and seven basic axioms: three to provide a recursive definition of
     'form', three common notions (so to speak) to power symbol manipulation,
     and a commutativity axiom. Metamath does not distinguish definitions from
     proper axioms.
  $)

  $( Recursive definition of LoF form (loff) -----------------------------
     1. Empty space is a loff.
     2. If ` p ` is a loff, enclosing it in brackets is a loff.
     3. If ` p ` and ` q ` are loffs, juxtaposing them is a loff.
  $)

  $( Empty space is a loff. $)
  lofdf-void $a loff $.

  $( If ` p ` is a loff, then ` ` [ p ` ] ` is a loff. $)
  lofdf-encl $a loff `[ p `] $.

  $( If ` p ` and ` q ` are loffs, then ` p q ` is a loff. $)
  lofdf-juxt $a loff p q $.


  $( Common Notions --------------------------------------------
     One goal of lof.mm is exploring the minimal basis for a boundary algebra.
     The next 3 axioms are the required machinery of symbol manipulation.
  $)

  ${
    lofax-euc.1 $e |- `[ `[ p `] `[ q `] `] `[ p q `] $.
    lofax-euc.2 $e |- `[ `[ r `] `[ q `] `] `[ r q `] $.
    $( We read this as:  If ` p ` is equivalent to ` q ` and ` r ` is
       equivalent to ` q ` , then we can assert that ` p ` is equivalent to
       ` r ` . $)
    lofax-euc $a |- `[ `[ p `] `[ r `] `] `[ p r `] $.
  $}

  ${
    lofax-beq.1 $e |- `[ `[ p `] `[ q `] `] `[ p q `] $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    lofax-beq $a |- `[ `[ `[ p `] `] `[ `[ q `] `] `] `[ `[ p `] `[ q `] `] $.
  $}

  ${
    lofax-sub.1 $e |- `[ `[ p `] `[ q `] `] `[ p q `] $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    lofax-sub $a |- `[ `[ p v `] `[ q v `] `] `[ p v q v `] $.
  $}
  $( PLEASE PUT DESCRIPTION HERE. $)
  lofax-cmm $a |- `[ `[ p q `] `[ q p `] `] `[ p q q p `] $.


  $( Theorems -------------------------------------------------------- The
     symbol '=' is never defined but it will turn out to obey the expected laws
     of an equivalence relation.  Specifically, from the common notion that two
     things equal to the same thing are equal to each other and from the
     commutativity of LoF, we derive the reflexivity, symmetry, and
     transitivity of '='.  Note that such a derivation is not possible in a
     traditional formal system without additional axioms -- it is the ability
     to reference the empty (or void) form that allows it here. $)
  lofidU $p |- `[ `[ p `] `[ p `] `] `[ p p `] $=
    lfp lofdf-void lofax-cmm $.
    $( [26-Jan-2017] $)


  ${
    lofsymU.1 $e |- `[ `[ p `] `[ q `] `] `[ p q `] $.
    $( '=' is symmetric. $)
    lofsymU $p |- `[ `[ q `] `[ p `] `] `[ q p `] $=
      lfq lfq lfp lfq lofidU lofsymU.1 lofax-euc $.
      $( [26-Jan-2017] $)
  $}

  ${
    loftransU.1 $e |- `[ `[ p `] `[ q `] `] `[ p q `] $.
    loftransU.2 $e |- `[ `[ q `] `[ r `] `] `[ q r `] $.
    $( '=' is transitive. $)
    loftransU $p |- `[ `[ p `] `[ r `] `] `[ p r `] $=
      lfp lfq lfr loftransU.1 lfq lfr loftransU.2 lofsymU lofax-euc $.
      $( [26-Jan-2017] $)
  $}

  $( Introducing the notion of lof equality. $)
  $c `= $.

  ${
    lofdf-NtoU.1 $e |- p `= q $.
    $( What equality means in terms of LoF's unitary formalism. $)
    lofdf-NtoU $a |- `[ `[ p `] `[ q `] `] `[ p q `] $.
  $}

  ${
    lofdf-UtoN.1 $e |- `[ `[ p `] `[ q `] `] `[ p q `] $.
    $( Translating LoF unitary form into normal form. $)
    lofdf-UtoN $a |- p `= q $.
  $}


  ${
    lofeuc.1 $e |- p `= q $.
    lofeuc.2 $e |- r `= q $.
    $( Two things equal to the same thing are equal to each other.  This is
       Euclid's first Common Notion and, in an equational logic, this and its
       sibling, transitivity, are the main engine of derivation. $)
    lofeuc $p |- p `= r $=
      lfp lfr lfp lfq lfr lfp lfq lofeuc.1 lofdf-NtoU lfr lfq lofeuc.2
      lofdf-NtoU lofax-euc lofdf-UtoN $.
      $( [26-Jan-2017] $)
  $}


  ${
    lofbeq.1 $e  |- p `= q $.
    $( Enclosing equal forms leaves equal forms. $)
    lofbeq $p |- `[ p `] `= `[ q `] $=
      lfp lofdf-encl lfq lofdf-encl lfp lfq lfp lfq lofbeq.1 lofdf-NtoU
      lofax-beq lofdf-UtoN $.
      $( [26-Jan-2017] $)
  $}


  ${
    lofsub.1 $e |- p `= q $.
    $( Juxtaposing the same form with equal forms leaves equal forms. $)
    lofsub $p |- p v `= q v $=
      lfp lfv lofdf-juxt lfq lfv lofdf-juxt lfp lfq lfv lfp lfq lofsub.1
      lofdf-NtoU lofax-sub lofdf-UtoN $.
      $( [26-Jan-2017] $)
  $}

  $( Commutativity of LoF. $)
  lofcmm $p |- p q `= q p $=
    lfp lfq lofdf-juxt lfq lfp lofdf-juxt lfp lfq lofax-cmm lofdf-UtoN $.
    $( [26-Jan-2017] $)

  $( From the common notion that two
     things equal to the same thing are equal to each other and from the
     commutativity of LoF, we derive the reflexivity, symmetry, and
     transitivity of '='.  Note that such a derivation is not possible in a
     traditional formal system without additional axioms -- it is the ability
     to reference the empty (or void) form that allows it here. $)

  $( ` ` = ` is reflexive. $)
  lofid $p |- p `= p $=
    lfp lofdf-void lofcmm $.
    $( [6-Sep-2015] $)

  ${
    lofsym.1 $e |- p `= q $.
    $( ` ` = ` is symmetric. $)
    lofsym $p |- q `= p $=
      lfq lfq lfp lfq lofid lofsym.1 lofeuc $.
      $( [2-Sep-2015] $)
  $}

  ${
    loftrans.1 $e |- p `= q $.
    loftrans.2 $e |- q `= r $.
    $( ` ` = ` is transitive. $)
    loftrans $p |- p `= r $=
      lfp lfq lfr loftrans.1 lfq lfr loftrans.2 lofsym lofeuc $.
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
    lofeucr.1 $e |- p `= q $.
    lofeucr.2 $e |- p `= r $.
    $( A commuted - or reversed - version of ~ lofeuc. $)
    lofeucr $p |- q `= r $=
      lfq lfp lfr lfp lfq lofeucr.1 lofsym lofeucr.2 loftrans $.
      $( [2-Sep-2015] $)
  $}

  ${
    lofsubr.1 $e |- p `= q $.
    $( A commuted version of lofsub. $)
    lofsubr $p |- u p `= u q $=
      lfq lfu lofdf-juxt lfu lfp lofdf-juxt lfu lfq lofdf-juxt lfp lfu
      lofdf-juxt lfq lfu lofdf-juxt lfu lfp lofdf-juxt lfp lfq lfu lofsubr.1
      lofsub lfp lfu lofcmm lofeucr lfq lfu lofcmm lofeucr $.
      $( [2-Sep-2015] $)
  $}

  $( More versions of the substitution principle. Our lack of access to the
     implicit commutativity of 2D forces us to spell out each case. $)
  ${
    lofsubst.1 $e |- p `= q $.
    $( PLEASE PUT DESCRIPTION HERE. $)
    lofsubst $p |- u p v `= u q v $=
      lfp lfv lofdf-juxt lfq lfv lofdf-juxt lfu lfp lfq lfv lofsubst.1 lofsub
      lofsubr $.
      
    $( [2-Sep-2015] $)
    lofsubstr $p |- u p v `= v q u $=
      lfu lfp lofdf-juxt lfv lofdf-juxt lfu lfv lofdf-juxt lfq lofdf-juxt lfv
      lfq lofdf-juxt lfu lofdf-juxt lfp lfv lofdf-juxt lfv lfq lofdf-juxt lfu
      lfp lfv lofdf-juxt lfq lfv lofdf-juxt lfv lfq lofdf-juxt lfp lfq lfv
      lofsubst.1 lofsub lfq lfv lofcmm loftrans lofsubr lfu lfv lfq lofdf-juxt
      lofcmm loftrans $.
      
    $( [2-Sep-2015] $)
    lofsubb1 $p |- w `[ u p v `] x `= w `[ u q v `] x $=
      lfu lfp lofdf-juxt lfv lofdf-juxt lofdf-encl lfu lfq lofdf-juxt lfv
      lofdf-juxt lofdf-encl lfw lfx lfu lfp lofdf-juxt lfv lofdf-juxt lfu lfq
      lofdf-juxt lfv lofdf-juxt lfp lfq lfu lfv lofsubst.1 lofsubst lofbeq
      lofsubst $.
      
    $( [2-Sep-2015] $)
    lofsubb2 $p |- w `[ u p v `] x `= w `[ v q u `] x $=
      lfu lfp lofdf-juxt lfv lofdf-juxt lofdf-encl lfv lfq lofdf-juxt lfu
      lofdf-juxt lofdf-encl lfw lfx lfu lfp lofdf-juxt lfv lofdf-juxt lfv lfq
      lofdf-juxt lfu lofdf-juxt lfp lfq lfu lfv lofsubst.1 lofsubstr lofbeq
      lofsubst $.
      $( [2-Sep-2015] $)
  $}

  ${
    lofrep.1 $e |- p `= q $.
    lofrep.2 $e |- u p v `= y $.
    $( Direct substitution into an equation. $)
    lofrep $p |- u q v `= y $=
      lfu lfp lofdf-juxt lfv lofdf-juxt lfu lfq lofdf-juxt lfv lofdf-juxt lfy
      lfp lfq lfu lfv lofrep.1 lofsubst lofrep.2 lofeucr $.
      $( [18-Sep-2015] $)
  $}

  ${
    lofreps.1 $e |- p `= q $.
    lofreps.2 $e |- y `= u p v $.
    $( Direct substitution into a (switched) equation. $)
    lofreps $p |- y `= u q v $=

    lfu lfq lofdf-juxt lfv lofdf-juxt   lfy
    lfp lfq lfu lfv lfy
    lofreps.1
    lfy lfu lfp lofdf-juxt lfv lofdf-juxt
    lofreps.2 lofsym
    lofrep
    lofsym
    $.
  $}

  ${
    lofrepbx.1 $e |- p `= q $.
    lofrepbx.2 $e |- w `[ u p v `] x `= y $.
    $( Direct substitution into a bounded-form equation. $)
    lofrepbx $p |- w `[ u q v `] x `= y $=
      lfw lfu lfp lofdf-juxt lfv lofdf-juxt lofdf-encl lofdf-juxt lfx
      lofdf-juxt lfw lfu lfq lofdf-juxt lfv lofdf-juxt lofdf-encl lofdf-juxt
      lfx lofdf-juxt lfy lfp lfq lfu lfv lfw lfx lofrepbx.1 lofsubb1 lofrepbx.2
      lofeucr $.
      $( [18-Sep-2015] $)
  $}

  ${
    lofrepbxs.1 $e |- p `= q $.
    lofrepbxs.2 $e |- y `= w `[ u p v `] x $.
    $( Direct substitution into a (switched) bounded-form equation. $)
    lofrepbxs $p |- y `= w `[ u q v `] x $=
    lfw lfu lfq lofdf-juxt lfv lofdf-juxt lofdf-encl lofdf-juxt lfx lofdf-juxt
    lfy
    lfp lfq
    lfu lfv lfw lfx lfy
    
    lofrepbxs.1
    lfy  lfw lfu lfp lofdf-juxt lfv lofdf-juxt lofdf-encl lofdf-juxt lfx lofdf-juxt
    lofrepbxs.2 lofsym
    lofrepbx
    lofsym
    $.
  $}

  $( This theorem allows a slightly quicker proof of lem3.3.
  ${
    lofrepbd.1  $e |- p `= q $.
    lofrepbd.2  $e |- `[ `[ u p v `] `] `= y $.
    @( Direct substitution into a double bounded-form equation. @)
    lofrepbd    $p |- `[ `[ u q v `] `] `= y $=
      ( lofdf-juxt lofdf-encl lofdf-void lofsubb1 lofbeq lofeucr ) CAHDHIZICBHD
      HIZIENOABCDJJFKLGM $.
      @( [3-Oct-2015] @)
  $}
  $)

  ${
    lofquad.1 $e |- p `= q $.
    lofquad.2 $e |- r `= s $.
    $( Double substitution of equivalent forms. $)
    lofquad $p |- p r `= q s $=
      lfp lfr lofdf-juxt lfq lfr lofdf-juxt lfq lfs lofdf-juxt lfp lfq
      lofdf-void lfr lofquad.1 lofsubst lfr lfs lfq lofdf-void lofquad.2
      lofsubst loftrans $.
      $( [2-Sep-2015] $)
  $}

  ${
    lofins.1 $e |- p q `= r s $.
    $( Insert the same form into two equivalent forms. $)
    lofins $p |- p v q `= r v s $=
      lfp lfv lofdf-juxt lfq lofdf-juxt lfv lfr lofdf-juxt lfs lofdf-juxt lfr
      lfv lofdf-juxt lfs lofdf-juxt lfp lfv lofdf-juxt lfq lofdf-juxt lfv lfp
      lofdf-juxt lfq lofdf-juxt lfv lfr lofdf-juxt lfs lofdf-juxt lfp lfv
      lofdf-juxt lfv lfp lofdf-juxt lfq lfp lfv lofcmm lofsub lfp lfq
      lofdf-juxt lfr lfs lofdf-juxt lfv lofins.1 lofsubr loftrans lfv lfr
      lofdf-juxt lfr lfv lofdf-juxt lfs lfv lfr lofcmm lofsub loftrans $.
      $( [3-Sep-2015] $)
  $}

  $( Extended commutativity. $)
  lofcmmx $p  |- u p v q w `= u q v p w $=
    lfp lfv lofdf-juxt lfq lofdf-juxt lfq lfv lofdf-juxt lfp lofdf-juxt lfu lfw
    lfp lfq lfq lfp lfv lfp lfq lofcmm lofins lofsubst $.
    $( [3-Sep-2015] $)

  $( Bounded and extended commutativity. $)
  lofcmmbx $p |- x `[ u p v q w `] y `= x `[ u q v p w `] y $=
    lfp lfv lofdf-juxt lfq lofdf-juxt lfq lfv lofdf-juxt lfp lofdf-juxt lfu lfw
    lfx lfy lfv lfv lfp lfq lfv lofid lofsubstr lofsubb1 $.
    $( [2-Sep-2015] $)

  ${
    lofquadbx.1 $e |- p `= q $.
    lofquadbx.2 $e |- r `= s $.
    $( Double substitution into a bounded and extended form. $)
    lofquadbx $p |- x `[ u p v r w `] y `= x `[ u q v s w `] y $=
      lfp lfv lofdf-juxt lfr lofdf-juxt lfq lfv lofdf-juxt lfs lofdf-juxt lfu
      lfw lfx lfy lfp lfr lfq lfs lfv lfp lfq lfr lfs lofquadbx.1 lofquadbx.2
      lofquad lofins lofsubb1 $.
      $( [3-Sep-2015] $)
  $}

  $( It's hard to know where to stop with auxiliary theorems. Had we choosen

     to prove the two additional statements:

     tranxb.1  $e |- p `= q $.
     tranxb.2  $e |- r `= q $.
     tranxb    $p |- x ( v p u ) w `= w ( u r v ) x $.

     tranrxb.1  $e |- p `= q $.
     tranrxb.2  $e |- p `= r $.
     tranrxb    $p |- x ( v q u ) w `= w ( u r v ) x $.

     we could have reduced significantly the proof of theorem c9.0. $)


  $( Position. $)
  j1.0 $a |- `[ `[ p `] p `] `= $.

  $( Transposition. $)
  j2.0 $a |- `[ `[ p r `] `[ q r `] `] `= `[ `[ p `] `[ q `] `] r $.

  $( System_0 consequences ------------------------------------ $)

  $( Reflexion. $)
  c1.0 $p |- `[ `[ p `] `] `= p $=
    lfp lofdf-encl lofdf-encl lfp lofdf-encl lofdf-encl lfp lofdf-juxt
    lofdf-encl lfp lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    lfp lfp lofdf-encl lofdf-encl lfp lfp lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl lofdf-encl lfp lofdf-encl lofdf-encl lfp lofdf-juxt lofdf-encl
    lfp lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-encl lofdf-encl lfp lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt
    lofdf-encl lfp lfp lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lfp lfp lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-encl
    lfp lofdf-encl lofdf-encl lfp lofdf-encl lfp lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl lfp lfp lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt
    lofdf-encl lfp lfp lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lfp lofdf-encl lofdf-encl lfp lofdf-encl lofdf-encl lfp
    lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl lofdf-juxt lfp
    lofdf-encl lfp lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lfp lfp
    lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl
    lofdf-encl lofdf-juxt lfp lofdf-encl lofdf-encl lfp lofdf-encl lofdf-encl
    lfp lofdf-encl lofdf-juxt lofdf-encl lofdf-void lfp lofdf-encl lofdf-encl
    lfp lofdf-encl j1.0 lofsub lofsym lfp lofdf-encl lfp lfp lofdf-encl
    lofdf-encl j2.0 lofeuc lfp lofdf-encl lfp lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl lfp lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl
    lofdf-void lfp lfp lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-void
    lofdf-void lfp lofdf-encl lfp lofdf-encl lofdf-encl lofdf-void lofdf-void
    lofdf-void lofdf-void lofdf-void lofcmmbx lofsubb1 loftrans lfp lofdf-encl
    lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lofdf-void lofdf-void lfp
    lfp lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-void lofdf-void lfp
    lofdf-encl j1.0 lofsubb1 loftrans lfp lfp lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl lfp lofdf-encl lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-void
    lfp lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-void lofdf-void lofdf-void
    lofdf-void lofdf-void lfp lfp lofdf-encl lofdf-encl lofdf-void lofdf-void
    lofdf-void lofdf-void lofdf-void lofcmmbx lfp lofdf-encl lfp lofdf-juxt
    lofdf-encl lofdf-void lfp j1.0 lofsym lofquadbx loftrans lfp lofdf-encl
    lofdf-encl lfp lofdf-juxt lofdf-encl lfp lofdf-encl lfp lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl lofdf-encl lfp
    lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-juxt lfp lfp
    lofdf-encl lofdf-encl lfp lofdf-encl lfp j2.0 lfp lofdf-encl lofdf-encl
    lofdf-encl lfp lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-void lfp
    lfp lofdf-encl lofdf-encl j1.0 lofsub loftrans loftrans $.
    $( [6-Sep-2015] $)

  $( Generation. $)
  c2.0 $p |- `[ p q `] q `= `[ p `] q $=
    lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfq lofdf-encl lfq lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lfp lfq lofdf-juxt lofdf-encl lfq
    lofdf-juxt lfp lofdf-encl lfq lofdf-juxt lfp lofdf-encl lfq lofdf-juxt
    lofdf-encl lfq lofdf-encl lfq lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    lfp lofdf-encl lofdf-encl lfq lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    lfq lofdf-juxt lfp lfq lofdf-juxt lofdf-encl lfq lofdf-juxt lfp lofdf-encl
    lfq lofdf-encl lfq j2.0 lfp lofdf-encl lofdf-encl lfp lfq lofdf-encl
    lofdf-encl lfq lofdf-void lofdf-void lofdf-void lofdf-void lfq lfp c1.0 lfq
    c1.0 lofquadbx loftrans lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfq
    lofdf-encl lfq lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl
    lfq lofdf-juxt lofdf-encl lofdf-encl lfp lofdf-encl lfq lofdf-juxt lfq
    lofdf-encl lfq lofdf-juxt lofdf-encl lofdf-void lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lofdf-void lofdf-void lofdf-void lfq j1.0 lofsubb1
    lfp lofdf-encl lfq lofdf-juxt c1.0 loftrans lofeucr $.
    $( [6-Sep-2015] $)

  $( Integration. $)
  c3.0 $p |- `[ `] p `= `[ `] $=
    lfp lofdf-encl lfp lofdf-juxt lofdf-void lofdf-encl lfp lofdf-juxt
    lofdf-void lofdf-encl lofdf-void lfp c2.0 lfp lofdf-encl lfp lofdf-juxt
    lofdf-encl lofdf-encl lfp lofdf-encl lfp lofdf-juxt lofdf-void lofdf-encl
    lfp lofdf-encl lfp lofdf-juxt c1.0 lfp lofdf-encl lfp lofdf-juxt lofdf-encl
    lofdf-void lfp j1.0 lofbeq lofeucr lofeucr $.
    $( [6-Sep-2015] $)

  $( Iteration. $)
  c5.0 $p |- p p `= p $=
    lfp lofdf-encl lfp lofdf-juxt lofdf-encl lfp lofdf-juxt lfp lfp lofdf-juxt
    lfp lfp lofdf-encl lfp lofdf-juxt lofdf-encl lfp lofdf-juxt lfp lofdf-encl
    lofdf-encl lfp lofdf-juxt lfp lfp lofdf-juxt lfp lofdf-encl lfp c2.0 lfp
    lofdf-encl lofdf-encl lfp lofdf-void lfp lfp c1.0 lofsubst loftrans lfp
    lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-void lofdf-void lfp lfp j1.0
    lofsubst lofeucr $.
    $( [6-Sep-2015] $)

  $( Occultation. $)
  c4.0 $p |- `[ `[ p `] q `] p `= p $=
    lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfp lofdf-juxt lofdf-void
    lofdf-encl lofdf-encl lfp lofdf-juxt lfp lfp lofdf-encl lfq lofdf-juxt
    lofdf-encl lfp lofdf-juxt lofdf-void lofdf-encl lfq lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl lfp lofdf-juxt lofdf-void lofdf-encl lofdf-encl lfp
    lofdf-juxt lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfp lofdf-juxt lfp
    lofdf-encl lfq lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    lofdf-void lofdf-encl lfq lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-juxt lfp lfp lofdf-juxt lofdf-encl lfq lofdf-encl lfp lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl
    lfp lofdf-juxt lfp lofdf-encl lfq lofdf-encl lfp lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl lfp lfp lofdf-juxt lofdf-encl lfq lofdf-encl lfp
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-encl
    lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-juxt lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lfp lofdf-juxt lfp lfq lofdf-encl lfp j2.0 lfq
    lofdf-encl lofdf-encl lfq lfp lofdf-encl lofdf-void lofdf-void lfp lfq c1.0
    lofsubb1 loftrans lfp lfp lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-void
    lfq lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-void lofdf-void lfp lfp
    lofdf-juxt lfp lofdf-void lofdf-void lofdf-void lofdf-void lfp c5.0
    lofsubb1 lofsubb1 lofeucr lofdf-void lfq lofdf-encl lfp j2.0 loftrans
    lofdf-void lofdf-encl lfq lofdf-encl lofdf-encl lofdf-juxt lofdf-void
    lofdf-encl lofdf-void lofdf-void lofdf-void lfp lfq lofdf-encl lofdf-encl
    c3.0 lofsubb1 loftrans lofdf-void lofdf-encl lofdf-encl lofdf-void
    lofdf-void lfp lofdf-void c1.0 lofsubst loftrans $.
    $( [6-Sep-2015] $)

  $( Extension. $)
  c6.0 $p |- `[ `[ p `] `[ q `] `] `[ `[ p `] q `] `= p $=
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lofdf-encl lfp lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-encl lfp lofdf-encl lfq
    lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl
    lofdf-juxt lfp lofdf-encl lofdf-encl lfp lofdf-encl lfq lofdf-encl
    lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl lofdf-juxt
    c1.0 lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-encl lfq lofdf-encl
    lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-juxt
    lofdf-encl lfp lofdf-encl lofdf-encl lfp lofdf-encl lfq lofdf-encl
    lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lfq lofdf-encl lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl
    lfp lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-juxt
    lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    lfq lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lfq lfp lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lofdf-encl lfq
    lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-juxt lfp lofdf-encl
    lfq lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lfp lofdf-encl
    lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfq lfp
    lofdf-encl lofdf-juxt lofdf-encl lofdf-void lofdf-void lofdf-void
    lofdf-void lofdf-void lfp lofdf-encl lfq lofdf-encl lofdf-void lofdf-void
    lofdf-void lofdf-void lofdf-void lofcmmbx lfp lofdf-encl lfq lofdf-void
    lofdf-void lofdf-void lofdf-void lofdf-void lofcmmbx lofquadbx lfq
    lofdf-encl lfq lfp lofdf-encl j2.0 loftrans lofbeq lfq lofdf-encl
    lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-void lofdf-void lfp
    lofdf-encl lofdf-void lofdf-void lfq lofdf-encl j1.0 lofsubb1 loftrans
    lofeucr lfp c1.0 loftrans $.
    $( [6-Sep-2015] $)

  $( Echelon. $)
  c7.0 $p |- `[ `[ `[ p `] q `] r `] `= `[ p r `] `[ `[ q `] r `] $=
    lfp lfr lofdf-juxt lofdf-encl lfq lofdf-encl lfr lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl
    lfr lofdf-juxt lofdf-encl lfp lfr lofdf-juxt lofdf-encl lfq lofdf-encl lfr
    lofdf-juxt lofdf-encl lofdf-juxt lfp lfr lofdf-juxt lofdf-encl lfq
    lofdf-encl lfr lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-encl lfp
    lofdf-encl lfq lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lfr lofdf-juxt
    lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt
    lofdf-encl lfp lfr lofdf-juxt lofdf-encl lfq lofdf-encl lfr lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl lfr lofdf-juxt lfp lfq lofdf-encl lfr j2.0 lofbeq lfp
    lofdf-encl lfq lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lfr lofdf-juxt
    lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lfq lofdf-encl
    lofdf-encl lfq lfp lofdf-encl lofdf-void lofdf-void lfr lfq c1.0 lofsubb1
    lofbeq loftrans lfp lfr lofdf-juxt lofdf-encl lfq lofdf-encl lfr lofdf-juxt
    lofdf-encl lofdf-juxt c1.0 lofeucr $.
    $( [6-Sep-2015] $)

  $( Modified transposition. $)
  c8.0 $p |- `[ `[ p `] `[ q s `] `[ r s `] `] 
             `= `[ `[ p `] `[ q `] `[ r `] `] `[ `[ p `] `[ s `] `] $=
    lfp lofdf-encl lfq lfs lofdf-juxt lofdf-encl lofdf-juxt lfr lfs lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lfr lofdf-encl lofdf-juxt
    lofdf-encl lfs lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lfr lofdf-encl lofdf-juxt
    lofdf-encl lfp lofdf-encl lfs lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lfq lfs lofdf-juxt lofdf-encl lfr lfs lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lofdf-encl lfq lfs lofdf-juxt lofdf-encl lfr lfs lofdf-juxt
    lofdf-encl lofdf-juxt lfp lofdf-encl lofdf-void lofdf-void lofdf-void lfq
    lofdf-encl lfr lofdf-encl lofdf-juxt lofdf-encl lfs lofdf-juxt lofdf-encl
    lfp lofdf-encl lofdf-juxt lofdf-encl lfq lfs lofdf-juxt lofdf-encl lfr lfs
    lofdf-juxt lofdf-encl lofdf-juxt c1.0 lfq lfs lofdf-juxt lofdf-encl lfr lfs
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-encl lfq lofdf-encl lfr
    lofdf-encl lofdf-juxt lofdf-encl lfs lofdf-juxt lofdf-encl lfp lofdf-encl
    lofdf-void lofdf-void lofdf-void lfq lfs lofdf-juxt lofdf-encl lfr lfs
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lfr lofdf-encl
    lofdf-juxt lofdf-encl lfs lofdf-juxt lfq lfr lfs j2.0 lofbeq lofsubb2
    lofrepbx lfq lofdf-encl lfr lofdf-encl lofdf-juxt lofdf-encl lfs lofdf-juxt
    lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lfr
    lofdf-encl lofdf-juxt lfp lofdf-encl lofdf-juxt lofdf-encl lfs lofdf-encl
    lfp lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq
    lofdf-encl lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl
    lfs lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfr
    lofdf-encl lofdf-juxt lfs lfp lofdf-encl c7.0 lfq lofdf-encl lfr lofdf-encl
    lofdf-juxt lfp lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-encl lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lfs lofdf-encl
    lfp lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfs lofdf-encl
    lofdf-juxt lofdf-encl lfq lofdf-encl lfr lofdf-encl lofdf-juxt lfp
    lofdf-encl lofdf-void lofdf-void lofdf-void lofdf-void lofdf-void lofcmmbx
    lfs lofdf-encl lfp lofdf-encl lofdf-void lofdf-void lofdf-void lofdf-void
    lofdf-void lofcmmbx lofquad loftrans loftrans $.
    $( [6-Sep-2015] $)

  $( Crosstransposition. $)
  c9.0 $p |- `[ `[ `[ q `] `[ p `] `] `[ `[ r `] `[ p `] `]
             `[ `[ s `] p `] `[ `[ t `] p `] `]
             `= `[ `[ p `] q r `] `[ p s t `] $=
    lfq lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lfr lofdf-encl lfp
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfs lofdf-encl lfp lofdf-juxt
    lofdf-encl lofdf-juxt lft lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lfs lft lofdf-juxt lofdf-encl lfp lofdf-juxt lofdf-encl lfq
    lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfr lofdf-encl
    lfp lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl
    lfq lofdf-juxt lfr lofdf-juxt lofdf-encl lfp lfs lofdf-juxt lft lofdf-juxt
    lofdf-encl lofdf-juxt lfs lofdf-encl lfp lofdf-juxt lofdf-encl lft
    lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt lfs lft lofdf-juxt
    lofdf-encl lfp lofdf-juxt lofdf-encl lfq lofdf-encl lfp lofdf-encl
    lofdf-juxt lofdf-encl lfr lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-void lofdf-void lofdf-void lfs lofdf-encl lfp lofdf-juxt
    lofdf-encl lft lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    lofdf-encl lfs lofdf-encl lfp lofdf-juxt lofdf-encl lft lofdf-encl lfp
    lofdf-juxt lofdf-encl lofdf-juxt lfs lft lofdf-juxt lofdf-encl lfp
    lofdf-juxt lofdf-encl lfs lofdf-encl lfp lofdf-juxt lofdf-encl lft
    lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt c1.0 lfs lofdf-encl lfp
    lofdf-juxt lofdf-encl lft lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lfs lft lofdf-juxt lofdf-encl lfp lofdf-juxt lfs lofdf-encl lfp
    lofdf-juxt lofdf-encl lft lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lfs lofdf-encl lofdf-encl lft lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl lfp lofdf-juxt lfs lft lofdf-juxt lofdf-encl lfp lofdf-juxt lfs
    lofdf-encl lft lofdf-encl lfp j2.0 lfs lofdf-encl lofdf-encl lfs lft
    lofdf-encl lofdf-encl lft lofdf-void lofdf-void lofdf-void lofdf-void lfp
    lfs c1.0 lft c1.0 lofquadbx loftrans lofbeq lofeucr lofsubb2 lfs lft
    lofdf-juxt lofdf-encl lfp lofdf-juxt lofdf-encl lfq lofdf-encl lfp
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfr lofdf-encl lfp lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfs lft lofdf-juxt lofdf-encl
    lfp lofdf-juxt lofdf-encl lfq lofdf-juxt lfr lofdf-juxt lofdf-encl lfs lft
    lofdf-juxt lfp lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq
    lofdf-juxt lfr lofdf-juxt lofdf-encl lfp lfs lofdf-juxt lft lofdf-juxt
    lofdf-encl lofdf-juxt lfs lft lofdf-juxt lofdf-encl lfp lofdf-juxt
    lofdf-encl lfq lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lfr lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    lfs lft lofdf-juxt lofdf-encl lfp lofdf-juxt lofdf-encl lfq lofdf-juxt lfr
    lofdf-juxt lofdf-encl lfs lft lofdf-juxt lofdf-encl lofdf-encl lfp
    lofdf-juxt lofdf-encl lofdf-juxt lfs lft lofdf-juxt lofdf-encl lfp
    lofdf-juxt lofdf-encl lfq lofdf-juxt lfr lofdf-juxt lofdf-encl lfs lft
    lofdf-juxt lfp lofdf-juxt lofdf-encl lofdf-juxt lfs lft lofdf-juxt
    lofdf-encl lfp lofdf-juxt lofdf-encl lfq lofdf-encl lfp lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lfr lofdf-encl lfp lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lfs lft lofdf-juxt lofdf-encl lfp
    lofdf-juxt lofdf-encl lfq lofdf-juxt lfr lofdf-juxt lofdf-encl lfs lft
    lofdf-juxt lofdf-encl lfp lofdf-juxt lofdf-encl lfp lofdf-juxt lofdf-encl
    lofdf-juxt lfs lft lofdf-juxt lofdf-encl lfp lofdf-juxt lofdf-encl lfq
    lofdf-juxt lfr lofdf-juxt lofdf-encl lfs lft lofdf-juxt lofdf-encl
    lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt lfs lft lofdf-juxt
    lofdf-encl lfp lofdf-juxt lofdf-encl lfq lofdf-encl lfp lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lfr lofdf-encl lfp lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lfs lft lofdf-juxt lofdf-encl lfp
    lofdf-juxt lofdf-encl lfq lofdf-juxt lfr lofdf-juxt lofdf-encl lfs lft
    lofdf-juxt lofdf-encl lfp lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lfs lft lofdf-juxt lofdf-encl lfp
    lofdf-juxt lofdf-encl lfq lofdf-juxt lfr lofdf-juxt lofdf-encl lfs lft
    lofdf-juxt lofdf-encl lfp lofdf-juxt lofdf-encl lfp lofdf-juxt lofdf-encl
    lofdf-juxt lfs lft lofdf-juxt lofdf-encl lfp lofdf-juxt lofdf-encl lfq
    lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfr lofdf-encl
    lfp lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfs lft
    lofdf-juxt lofdf-encl lfp lofdf-juxt lofdf-encl lfq lofdf-encl lofdf-encl
    lofdf-juxt lfr lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lfs lft
    lofdf-juxt lofdf-encl lfp lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lfs lft lofdf-juxt lofdf-encl lfp
    lofdf-juxt lofdf-encl lfq lofdf-juxt lfr lofdf-juxt lofdf-encl lfs lft
    lofdf-juxt lofdf-encl lfp lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lfs lft lofdf-juxt lofdf-encl lfp
    lofdf-juxt lfq lofdf-encl lfr lofdf-encl lfp lofdf-encl c8.0 lfq lofdf-encl
    lofdf-encl lfq lfr lofdf-encl lofdf-encl lfr lfs lft lofdf-juxt lofdf-encl
    lfp lofdf-juxt lofdf-encl lofdf-void lofdf-void lofdf-void lfs lft
    lofdf-juxt lofdf-encl lfp lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl lfq c1.0 lfr c1.0 lofquadbx loftrans lfp lofdf-encl
    lofdf-encl lfp lfs lft lofdf-juxt lofdf-encl lfp lofdf-juxt lofdf-encl
    lofdf-void lfs lft lofdf-juxt lofdf-encl lfp lofdf-juxt lofdf-encl lfq
    lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-void lfp c1.0 lofsubb1 loftrans
    lfs lft lofdf-juxt lofdf-encl lfp lofdf-juxt lofdf-encl lfp lofdf-juxt lfs
    lft lofdf-juxt lofdf-encl lofdf-encl lfp lofdf-juxt lofdf-void lofdf-void
    lfs lft lofdf-juxt lofdf-encl lfp lofdf-juxt lofdf-encl lfq lofdf-juxt lfr
    lofdf-juxt lofdf-encl lofdf-void lfs lft lofdf-juxt lofdf-encl lfp c2.0
    lofsubb1 loftrans lfs lft lofdf-juxt lofdf-encl lofdf-encl lfs lft
    lofdf-juxt lofdf-void lfp lfs lft lofdf-juxt lofdf-encl lfp lofdf-juxt
    lofdf-encl lfq lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-void lfs lft
    lofdf-juxt c1.0 lofsubb1 loftrans lfs lft lofdf-juxt lofdf-encl lfp
    lofdf-juxt lofdf-encl lfq lofdf-juxt lfr lofdf-juxt lfs lft lofdf-juxt lfp
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfs lft lofdf-juxt lfp
    lofdf-juxt lofdf-encl lofdf-juxt lfs lft lofdf-juxt lofdf-encl lfp
    lofdf-juxt lofdf-encl lfq lofdf-juxt lfr lofdf-juxt lofdf-encl lfs lft
    lofdf-juxt lfp lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq
    lofdf-juxt lfr lofdf-juxt lofdf-encl lfp lfs lofdf-juxt lft lofdf-juxt
    lofdf-encl lofdf-juxt lfs lft lofdf-juxt lofdf-encl lfp lofdf-juxt
    lofdf-encl lfq lofdf-juxt lfr lofdf-juxt lfs lft lofdf-juxt lfp lofdf-juxt
    lofdf-encl c2.0 lfs lft lofdf-juxt lofdf-encl lfp lofdf-juxt lofdf-encl lfq
    lofdf-juxt lfr lofdf-juxt lfs lft lofdf-juxt lfp lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl lfs lft lofdf-juxt lfp lofdf-juxt lofdf-encl
    lofdf-juxt lfp lfs lft lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfq
    lofdf-juxt lfr lofdf-juxt lfp lfs lofdf-juxt lft lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl lfs lft lofdf-juxt lfp lofdf-juxt lofdf-encl
    lofdf-juxt lfp lofdf-encl lfq lofdf-juxt lfr lofdf-juxt lofdf-encl lfp lfs
    lofdf-juxt lft lofdf-juxt lofdf-encl lofdf-juxt lfs lft lofdf-juxt
    lofdf-encl lfp lofdf-juxt lofdf-encl lfp lfs lft lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl lfs lft lofdf-juxt lfp lofdf-juxt lofdf-encl lfp lfs
    lofdf-juxt lft lofdf-juxt lofdf-encl lofdf-void lfq lfr lofdf-juxt
    lofdf-void lofdf-void lfs lft lofdf-juxt lfp lofdf-juxt lofdf-encl lfs lft
    lofdf-juxt lofdf-encl lfp lofdf-void lofdf-void lofdf-void lofdf-void
    lofdf-void lofcmmbx lfs lft lofdf-juxt lfp lofdf-void lofdf-void lofdf-void
    lofdf-void lofdf-void lofcmmbx lofquadbx lfp lofdf-encl lofdf-encl lfs lft
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-juxt lfr lofdf-juxt
    lfp lofdf-encl lofdf-encl lfs lofdf-juxt lft lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl lfs lft lofdf-juxt lfp lofdf-juxt lofdf-encl
    lofdf-juxt lfp lfs lft lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfq
    lofdf-juxt lfr lofdf-juxt lfp lfs lofdf-juxt lft lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl lfs lft lofdf-juxt lfp lofdf-juxt lofdf-encl
    lofdf-juxt lfp lofdf-encl lfq lofdf-juxt lfr lofdf-juxt lofdf-encl lfp lfs
    lofdf-juxt lft lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lofdf-encl
    lfs lft lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-juxt lfr
    lofdf-juxt lfp lfs lft lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfq
    lofdf-juxt lfr lofdf-juxt lfp lofdf-encl lofdf-encl lfs lofdf-juxt lft
    lofdf-juxt lofdf-encl lfp lfs lofdf-juxt lft lofdf-juxt lofdf-encl
    lofdf-void lofdf-void lofdf-void lofdf-void lfs lft lofdf-juxt lfp
    lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl lfp lofdf-void lfs lft
    lofdf-juxt lofdf-encl lofdf-void lfq lfr lofdf-juxt lfp c1.0 lofsubb1 lfp
    lofdf-encl lofdf-encl lfp lofdf-void lfs lft lofdf-juxt lofdf-void
    lofdf-void lfp c1.0 lofsubb1 lofquadbx lfp lofdf-encl lofdf-encl lfs lft
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-juxt lfr lofdf-juxt
    lfp lofdf-encl lofdf-encl lfs lofdf-juxt lft lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl lfs lft lofdf-juxt lfp lofdf-juxt lofdf-encl
    lofdf-juxt lfp lofdf-encl lofdf-encl lfs lft lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl lfs lofdf-juxt lft
    lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-juxt lfr lofdf-juxt lofdf-encl
    lfs lft lofdf-juxt lfp lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq
    lofdf-juxt lfr lofdf-juxt lofdf-encl lfp lfs lofdf-juxt lft lofdf-juxt
    lofdf-encl lofdf-juxt lfq lfr lofdf-juxt lfp lofdf-encl lofdf-encl lfs
    lofdf-juxt lft lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl lfs lft
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-void lofdf-void
    lofdf-void lfs lft lofdf-juxt lfp lofdf-juxt lofdf-encl lofcmmbx lfp
    lofdf-encl lofdf-encl lfs lft lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    lfp lofdf-encl lofdf-encl lfs lofdf-juxt lft lofdf-juxt lofdf-encl
    lofdf-juxt lfq lofdf-juxt lfr lofdf-juxt lofdf-encl lfs lft lofdf-juxt lfp
    lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-juxt lfr
    lofdf-juxt lofdf-encl lfs lft lofdf-juxt lfp lofdf-juxt lofdf-encl
    lofdf-juxt lfp lofdf-encl lfq lofdf-juxt lfr lofdf-juxt lofdf-encl lfp lfs
    lofdf-juxt lft lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lofdf-encl
    lfs lft lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl
    lofdf-encl lfs lofdf-juxt lft lofdf-juxt lofdf-encl lofdf-juxt lfp
    lofdf-encl lofdf-void lfq lfr lofdf-juxt lofdf-void lfs lft lofdf-juxt lfp
    lofdf-juxt lofdf-encl lfp lofdf-encl lfs lft lofdf-juxt c6.0 lofsubb1 lfs
    lft lofdf-juxt lfp lofdf-void lofdf-void lofdf-void lfp lofdf-encl lfq
    lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-void lofcmmbx loftrans loftrans
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
  c5.1 $a |- p p `= p $.
  $( PLEASE PUT DESCRIPTION HERE. $)
  c6.1 $a |- `[ `[ p `] `[ q `] `] `[ `[ p `] q `] `= p $.

  $( System_1 consequences ------------------------------------ $)

  $( Lemma for proof of c1.1.  Under the dual interpretation, this is mildly
     reminiscent of modus ponens:  (p & (p -> q)) ` = (p & q). $)
  lem1.1 $p |- p `[ `[ q `] p `] `= p q $=
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfp lofdf-encl lofdf-juxt
    lofdf-encl lfq lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt lofdf-juxt
    lfp lfq lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt lfp lfq lofdf-juxt
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfp lofdf-encl lofdf-juxt
    lofdf-encl lfq lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt lofdf-juxt
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfp lofdf-juxt lofdf-encl
    lofdf-juxt lfp lfq lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfp lofdf-encl lofdf-juxt
    lofdf-encl lfq lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt lofdf-juxt
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-juxt
    lofdf-encl lfq lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt lofdf-juxt
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfp lofdf-juxt lofdf-encl
    lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-encl lfq lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfp
    lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lfp lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl
    lfp lofdf-encl lfq lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq
    lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lfp lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp
    lofdf-encl lfq lofdf-juxt lofdf-encl lfq lofdf-encl lfp lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-juxt lfq lofdf-encl lfp lofdf-encl lofdf-juxt
    lofdf-encl lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfp lofdf-juxt lofdf-encl
    lfq lofdf-encl lfp lofdf-encl lofdf-void lofdf-void lofdf-void lofdf-void
    lofdf-void lofcmmbx lofsubst lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-encl lofdf-juxt lofdf-encl lofdf-void lfq lofdf-encl lfp lofdf-juxt
    lofdf-encl lofcmmx loftrans lfp lofdf-encl lfq lofdf-encl lofdf-juxt
    lofdf-encl lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lfq lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl c5.1 lofsub loftrans
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lofdf-juxt lfp lfq lofdf-encl lfp lofdf-juxt
    lofdf-encl lfp lfq c6.1 lofsub loftrans lfp lofdf-encl lfq lofdf-encl
    lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl lofdf-juxt
    lfp lfq lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lfp
    lofdf-juxt lofdf-encl lofdf-juxt lfq lfp lfq c6.1 lfq lfp c6.1 lofquad
    lofeucr $.
    
  $( [17-Sep-2015] $)
  c1.1 $p |- `[ `[ p `] `] `= p $=
    lofdf-void lfp lem1.1 $.
    $( [17-Sep-2015] $)

  $( The LoF I2 arithmetic initial.  This is also directly derivable from the
     basis by plugging void values into c6.1, followed by two applications of
     c5.1. $)
  i2.1 $p |- `[ `[ `] `] `= $=
    lofdf-void c1.1 $.
    $( [17-Sep-2015] $)

  $( One of the two equations from Basis_0. $)
  j1.1 $p |- `[ `[ p `] p `] `= $=
    lfp lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-void lofdf-encl lofdf-encl
    lofdf-void lfp lofdf-encl lfp lofdf-juxt lofdf-void lofdf-encl lfp
    lofdf-encl lfp lofdf-encl lofdf-encl lofdf-juxt lfp lofdf-encl lfp
    lofdf-juxt lofdf-void lofdf-encl lfp lofdf-encl lofdf-encl lfp lfp
    lofdf-encl lfp c1.1 lofsubr lfp lofdf-encl lofdf-encl lfp lofdf-encl
    lofdf-juxt lfp lofdf-encl lfp lofdf-encl lofdf-encl lofdf-juxt lofdf-void
    lofdf-encl lfp lofdf-encl lofdf-encl lfp lofdf-encl lofcmm lofdf-void
    lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lofdf-void
    lofdf-encl lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl
    lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-void lofdf-encl lofdf-void
    lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl
    lofdf-encl lofdf-void lofdf-encl lofdf-encl lfp lofdf-juxt lofdf-encl lfp
    lofdf-encl lofdf-void lofdf-encl lofdf-encl lofdf-void lofdf-void lfp
    lofdf-encl lofdf-void lofdf-void i2.1 lofsubb1 lofdf-void lofdf-encl
    lofdf-encl lofdf-void lofdf-void lfp lofdf-void lofdf-void i2.1 lofsubb1
    lofquad lofdf-void lofdf-encl lfp c6.1 lofeucr lofeucr lofeucr lofbeq i2.1
    loftrans $.
    
  $( [17-Sep-2015] $)
  c4.1 $p |- `[ `[ p `] q `] p `= p $=
    lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfp lofdf-juxt lfp lofdf-encl lfq
    lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl
    lofdf-juxt lfp lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-encl lfq lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-juxt lofdf-encl
    lfp lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-encl lfq lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq
    lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl
    lofdf-juxt lfp lofdf-void lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfp lfq
    c6.1 lofsubstr lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-juxt lofdf-encl
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl c5.1 lofsubr lofeucr lfp lfq c6.1 loftrans $.
    $( [18-Sep-2015] $)

  $( Corollary of c4.1 $)
  c4cor.1 $p |- `[ p q `] `[ p `] `= `[ p `] $=
    lfp lofdf-encl lofdf-encl lfq lofdf-juxt lofdf-encl lfp lofdf-encl
    lofdf-juxt lfp lfq lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-juxt lfp
    lofdf-encl lfp lofdf-encl lofdf-encl lfp lofdf-void lfq lofdf-void lfp
    lofdf-encl lfp c1.1 lofsubb1 lfp lofdf-encl lfq c4.1 lofeucr $.
    $( [18-Sep-2015] $)

  $( Corollary of c6.1 $)
  c6cor.1 $p |- `[ `[ p `] q `] `[ p q `] `= `[ q `] $=
    lfq lfp lofdf-juxt lfp lfq lofdf-juxt lofdf-void lofdf-void lfp lofdf-encl
    lfq lofdf-juxt lofdf-encl lofdf-void lfq lofdf-encl lfq lfp lofcmm lfq lfp
    lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-juxt lofdf-void lofdf-void
    lofdf-void lfq lfp lofdf-juxt lofdf-encl lfq lofdf-encl lfq lfp lofdf-encl
    lofcmm lfq lofdf-encl lofdf-encl lfq lofdf-void lfp lfq lfp lofdf-encl
    lofdf-juxt lofdf-encl lofdf-void lfq lofdf-encl lfq c1.1 lfq lofdf-encl
    lofdf-encl lfq lofdf-void lfp lofdf-encl lofdf-void lfq lofdf-encl
    lofdf-encl lfp lofdf-juxt lofdf-encl lfq lofdf-encl lfq c1.1 lfq lofdf-encl
    lfp c6.1 lofrepbx lofrepbx lofrepbx lofrepbx $.
    
  $( [22-Sep-2015] $)
  c7.1 $p |- `[ `[ `[ p `] q `] r `] `= `[ p r `] `[ `[ q `] r `] $=
    lfp lfr lofdf-juxt lofdf-encl lfq lofdf-encl lfr lofdf-juxt lofdf-encl
    lofdf-juxt lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt
    lofdf-encl lfr lfq lofdf-encl lofdf-juxt lfq lofdf-encl lfr lofdf-juxt
    lofdf-void lofdf-void lfp lfr lofdf-juxt lofdf-encl lofdf-void lfp
    lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lofdf-encl lfr lfq
    lofdf-encl lofcmm lfr lfp lofdf-juxt lfp lfr lofdf-juxt lofdf-void
    lofdf-void lofdf-void lfr lfq lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lofdf-encl lfr lfp
    lofcmm lfr lfq lofdf-encl lofdf-juxt lfp lofdf-encl lofdf-juxt lofdf-encl
    lfr lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfr lfq lofdf-encl
    lofdf-juxt lofdf-encl lfr lfp lofdf-juxt lofdf-encl lofdf-void lfp
    lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lofdf-encl lfr lfq
    lofdf-encl lofdf-juxt lfp lofdf-encl c4cor.1 lfp lofdf-encl lfr lofdf-juxt
    lfq lofdf-encl lofdf-juxt lfr lfq lofdf-encl lofdf-juxt lfp lofdf-encl
    lofdf-juxt lofdf-void lofdf-void lfr lfp lofdf-juxt lofdf-encl lfr lfq
    lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl
    lfr lofdf-juxt lofdf-encl lfp lofdf-encl lfr lfq lofdf-encl lofdf-juxt
    lofcmm lfr lfq lofdf-encl lofdf-juxt lofdf-encl lfr lfp lofdf-juxt
    lofdf-encl lfp lofdf-encl lfr lofdf-juxt lfq lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-juxt lfr lfp lofdf-juxt lofdf-encl lfp
    lofdf-encl lfr lofdf-juxt lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lfr lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-void lofdf-void
    lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lofdf-encl lfr lfq
    lofdf-encl lofdf-juxt lofdf-encl lfr lfp lofdf-juxt lofdf-encl lfp
    lofdf-encl lfr lofdf-juxt lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lofcmm lfr lfp lofdf-juxt lfq lofdf-juxt lofdf-encl lfr lfp lofdf-juxt
    lofdf-encl lofdf-juxt lfr lfp lofdf-juxt lofdf-encl lfr lfq lofdf-encl
    lofdf-juxt lofdf-encl lfp lofdf-encl lfr lofdf-juxt lfq lofdf-encl
    lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr
    lofdf-juxt lofdf-encl lfr lfp lofdf-juxt lfq c4cor.1 lfr lfq lofdf-encl
    lofdf-juxt lofdf-encl lfr lfp lofdf-juxt lfq lofdf-juxt lofdf-encl
    lofdf-juxt lfr lfp lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfr
    lofdf-juxt lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl
    lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lfr lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl
    lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lofdf-encl lfr lfq lofdf-encl
    lofdf-juxt lofdf-encl lfr lfp lofdf-juxt lfq lofdf-juxt lofdf-encl
    lofdf-juxt lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt
    lofdf-encl lfr lfp lofdf-juxt lofdf-encl lfp lofdf-encl lfr lofdf-juxt lfq
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-juxt
    lofdf-encl lfr lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-juxt
    lofdf-encl lfp lfq lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfr
    lofdf-void lofdf-void lfr lfp lofdf-juxt lfq lofdf-juxt lofdf-encl lfp
    lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lofdf-encl lfp lfq
    c6cor.1 lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lfr lfp
    lofdf-encl lfq lofdf-juxt lofdf-encl lofdf-juxt lofdf-void lfp lfq
    lofdf-juxt lofdf-encl lofdf-void lfr lfp lofdf-juxt lfq lofdf-juxt
    lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt
    lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofcmm lfp
    lofdf-encl lfq lofdf-juxt lofdf-encl lfp lofdf-juxt lfp lfr lfq lfp
    lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lfp lfq lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lofdf-void lfp lofdf-encl lfq lofdf-juxt
    lofdf-encl lfr lofdf-juxt lofdf-encl lfp lfq c4.1 lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lfr lofdf-juxt lfr lfp lofdf-encl lfq lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-void lfp lfq lofdf-juxt lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lfr lofdf-juxt lfp lfq lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl lofdf-void lfp lofdf-encl lfq lofdf-juxt lofdf-encl
    lfr lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr
    lofcmm lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lofdf-encl
    lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt
    lofdf-void lfp lfq lofdf-juxt lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr
    lofdf-juxt lfp lfq lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-void
    lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lofdf-encl lfp
    lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt c1.1 lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lfr lofdf-juxt lofdf-encl lofdf-encl lfp lofdf-encl
    lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lofdf-void lfp lfq lofdf-juxt
    lofdf-encl lofdf-void lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr
    lofdf-juxt lofdf-encl lofdf-encl lfp lfq lofdf-juxt lofdf-juxt lofdf-encl
    lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lofdf-encl lfp
    lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt c1.1 lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lfr lofdf-juxt lofdf-encl lfp lfq lofdf-juxt c6.1
    lofrepbx lofrepbx lofrepbx lofrepbx lofrepbx lofrepbx lfq lfp lofdf-encl
    lofdf-juxt lofdf-encl lfq lofdf-encl lofdf-juxt lfq lofdf-encl lfp
    lofdf-encl lfr lofdf-juxt lofdf-void lfr lfp lofdf-juxt lofdf-encl
    lofdf-void lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt
    lofdf-encl lfq lfp lofdf-encl c4cor.1 lfp lofdf-encl lfr lofdf-juxt lfp
    lofdf-encl lfq lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lofdf-juxt
    lfp lofdf-encl lfr lofdf-juxt lfq lfp lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt lfq lofdf-encl lofdf-juxt lofdf-void lofdf-void lfr lfp
    lofdf-juxt lofdf-encl lofdf-void lfp lofdf-encl lfq lofdf-juxt lofdf-encl
    lfr lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-void lofdf-void
    lofdf-void lfp lofdf-encl lfr lofdf-juxt lfq lofdf-encl lofcmmbx lfr lfp
    lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr
    lofdf-juxt lfp lofdf-encl lofdf-juxt lfq lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt lfr lfp lofdf-juxt lofdf-encl lfp lofdf-encl lfr lofdf-juxt lfp
    lofdf-encl lfq lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr
    lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfp
    lofdf-encl lofdf-void lfr lfq lofdf-encl lfr lfp lofdf-juxt lofdf-encl
    lofdf-void lofcmmbx lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-encl lfq lofdf-juxt lofdf-encl lofdf-juxt lfp lfr lofdf-void
    lofdf-void lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lfp
    lofdf-encl lofdf-juxt lfq lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl
    lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lofdf-encl lfp lfq c6.1 lfp
    lofdf-encl lfq lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-juxt
    lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl lofdf-juxt lfr
    lofdf-void lofdf-void lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr
    lofdf-juxt lfp lofdf-encl lofdf-juxt lfq lofdf-encl lofdf-juxt lofdf-encl
    lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lofdf-encl lfp
    lofdf-encl lfq lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-encl
    lofdf-juxt lofdf-encl lofcmm lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr
    lofdf-juxt lfr lfp lofdf-encl lfq lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-void lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-void
    lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lfp lofdf-encl
    lofdf-juxt lfq lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lfr lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lfr lofcmm lfp lofdf-encl lfq lofdf-juxt lofdf-encl
    lfr lofdf-juxt lofdf-encl lofdf-encl lfp lofdf-encl lfq lofdf-juxt
    lofdf-encl lfr lofdf-juxt lofdf-void lfp lofdf-encl lfq lofdf-encl
    lofdf-juxt lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    lofdf-void lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt
    lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt c1.1 lfp
    lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lofdf-encl lofdf-encl
    lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lofdf-void lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-void lfp lofdf-encl
    lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lofdf-encl lofdf-encl lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-juxt lofdf-encl lfp lofdf-encl
    lfq lofdf-juxt lofdf-encl lfr lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-juxt lofdf-encl lfr lofdf-juxt c1.1 lfp lofdf-encl lfq lofdf-juxt
    lofdf-encl lfr lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-encl
    lofdf-juxt c6.1 lofrepbx lofrepbx lofrepbx lofrepbx lofrepbx lofeucr
    lofrepbx lofrepbx lofquad lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfr
    lofdf-juxt lofdf-encl c5.1 loftrans lofrep lofrep lofrepbx lofrep lofrepbx
    lofrepbx lofsym $.
    $( [23-Sep-2015] $)

  $( The second of the two equations from Basis_0.  This completes the proof
     that Basis_1 is at least as powerful as Basis_0. $)
  j2.1 $p |- `[ `[ p `] `[ q `] `] r `= `[ `[ p r `] `[ q r `] `] $=
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfr lofdf-juxt
    lofdf-encl lofdf-encl lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl
    lfr lofdf-juxt lfp lfr lofdf-juxt lofdf-encl lfq lfr lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl
    lfr lofdf-juxt c1.1 lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfr
    lofdf-juxt lofdf-encl lfp lfr lofdf-juxt lofdf-encl lfq lfr lofdf-juxt
    lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl
    lfr lofdf-juxt lofdf-encl lfp lfr lofdf-juxt lofdf-encl lfq lofdf-encl
    lofdf-encl lfr lofdf-juxt lofdf-encl lofdf-juxt lfp lfr lofdf-juxt
    lofdf-encl lfq lfr lofdf-juxt lofdf-encl lofdf-juxt lfp lfq lofdf-encl lfr
    c7.1 lfq lofdf-encl lofdf-encl lfq lofdf-void lfr lfp lfr lofdf-juxt
    lofdf-encl lofdf-void lfq c1.1 lofsubb1 loftrans lofbeq lofeucr $.
    $( [23-Sep-2015] $)

$( =======================================================================

     System_2

     Having shown that C5 and C6 form a basis, I now show that C6 alone
     suffices. The derivation ends at the point where c5.2 is proved, since
     that establishes that Basis_2 is at least as powerful as Basis_1. $)

  $( Basis_2 --------------------------------------------- $)
  c6.2 $a |- `[ `[ p `] `[ q `] `] `[ `[ p `] q `] `= p $.

  $( System_2 consequences ------------------------------------ $)

  $( An important lemma used in the proof of c1.2. $)
  lem2.2 $p |- `[ p `] p `= `[ q `] q $=
    lfq lofdf-encl lfq lofdf-juxt lfp lofdf-encl lfp lofdf-juxt lfq lofdf-encl
    lfp lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lfp
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfq lfq lofdf-encl lofdf-void
    lfp lofdf-encl lfp lofdf-juxt lfq lfp lofdf-encl c6.2 lfp lofdf-encl lfq
    lofdf-encl lofdf-juxt lfq lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-void
    lofdf-void lfq lofdf-encl lfq lofdf-encl lfp lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-void lfp lofdf-encl lfp lofdf-juxt
    lfp lofdf-encl lfq lofdf-encl lofcmm lfp lofdf-encl lofdf-encl lfq
    lofdf-encl lofdf-juxt lfq lofdf-encl lfp lofdf-encl lofdf-encl lofdf-juxt
    lofdf-void lofdf-void lfq lofdf-encl lfp lofdf-encl lfq lofdf-encl
    lofdf-juxt lofdf-encl lfp lofdf-encl lfp lofdf-juxt lfp lofdf-encl
    lofdf-encl lfq lofdf-encl lofcmm lfq lofdf-encl lofdf-encl lfp lofdf-encl
    lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lofdf-encl lfp lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lofdf-void lfp lofdf-encl
    lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfp lofdf-juxt
    lfq lofdf-encl lfp lofdf-encl c6.2 lfp lofdf-encl lfp lofdf-juxt lfq
    lofdf-encl lofdf-encl lfp lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lfq
    lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp
    lofdf-encl lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl
    lfp lofdf-juxt lfq lofdf-encl lofdf-encl lfp lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl lfq lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt lfq lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt lfq lofdf-encl lofdf-encl lfp lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl lfq lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt lfp lofdf-encl lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lfp lofdf-encl lfp lofdf-juxt lfq lofdf-encl lofdf-encl lfp lofdf-encl
    lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl lfq lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-juxt lfq lofdf-encl lofdf-encl lfp lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl lfq lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt lfq lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt
    lofdf-encl lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-juxt lfp lofdf-encl lofdf-encl lfq lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl lfp lofdf-encl lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-juxt
    lfp lofdf-encl lfp lofdf-juxt lfq lofdf-encl lofdf-encl lfp lofdf-encl
    lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl lfq lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-juxt lfp lofdf-encl lofdf-encl lfq lofdf-encl lofdf-encl
    lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl lfq lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt lfp lofdf-encl lfp lofdf-encl lfq lofdf-encl
    lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt lfp lfp lofdf-encl lfq lofdf-encl c6.2 lfp lfq
    lofdf-encl c6.2 lofquad lfp lofdf-encl lofdf-encl lfq lofdf-encl lofdf-encl
    lofdf-juxt lfq lofdf-encl lofdf-encl lfp lofdf-encl lofdf-encl lofdf-juxt
    lofdf-void lofdf-void lofdf-void lfp lofdf-encl lofdf-encl lfq lofdf-encl
    lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt lfp lofdf-encl lofdf-encl lfq lofdf-encl lofdf-encl lofcmm
    lofsubb1 lofeucr lfp lofdf-encl lfq lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl lfq lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl
    lfq lofdf-encl lofdf-encl lfp lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    lfp lofdf-encl lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-encl lofdf-encl lofdf-juxt lfq lofdf-encl lofdf-encl lfp lofdf-encl
    lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-encl lofcmm lofbeq lofsubst
    loftrans lfp lofdf-encl lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfq
    lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl
    lofdf-encl lfp lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-void lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lofcmmx loftrans lofsym
    lofrep lofrepbx lofrepbx lofrep lofsym $.
    $( [24-Sep-2015] $)

  $( This is axiom B3 from Meguire. $)
  b3.2 $p |- `[ p `] p `= `[ `] $=
    lfp lofdf-void lem2.2 $.
    
  $( [18-Aug-2016] $)
  c1.2 $p |- `[ `[ p `] `] `= p $=
    lfp lofdf-encl lfp lofdf-encl lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    lfp lofdf-encl lfp lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lfp lofdf-encl lofdf-encl lfp lfp lofdf-encl lofdf-encl lfp lofdf-encl
    lofdf-juxt lfp lofdf-encl lfp lofdf-encl lofdf-encl lofdf-juxt lofdf-void
    lofdf-void lfp lofdf-encl lfp lofdf-encl lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl lofdf-void lfp lofdf-encl lofdf-encl lfp lofdf-encl lofdf-encl
    lfp lofdf-encl lofcmm lfp lofdf-encl lofdf-encl lofdf-encl lfp lofdf-encl
    lofdf-juxt lfp lofdf-encl lfp lofdf-encl lofdf-encl lofdf-encl lofdf-juxt
    lofdf-void lofdf-void lofdf-void lfp lofdf-encl lofdf-encl lfp lofdf-encl
    lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl lfp lofdf-encl lofdf-encl
    lofdf-encl lfp lofdf-encl lofcmm lfp lofdf-encl lofdf-encl lfp lofdf-encl
    lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl lofdf-encl lfp lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lofdf-encl lofdf-encl lfp
    lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl lfp lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-void lofdf-void lfp lofdf-encl
    lofdf-encl lfp lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl
    lfp lofdf-encl lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl
    lofcmm lfp lofdf-encl lofdf-encl lofdf-encl lfp lofdf-encl lofdf-encl
    lofdf-juxt lfp lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-void
    lofdf-void lofdf-void lfp lofdf-encl lofdf-encl lofdf-encl lfp lofdf-encl
    lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl lfp lofdf-encl lofdf-encl
    lfp lofdf-encl lem2.2 lfp lofdf-encl lofdf-encl lfp lofdf-encl c6.2
    lofrepbx lofrep lofrepbx lofrepbx lfp lfp lofdf-encl lofdf-encl c6.2
    lofeucr $.
    
  $( [25-Sep-2015] $)
  j1.2 $p |- `[ `[ p `] p `] `= $=
    lfp lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-void lofdf-encl lofdf-encl
    lofdf-void lfp lofdf-encl lfp lofdf-juxt lofdf-void lofdf-encl lfp b3.2
    lofbeq lofdf-void c1.2 loftrans $.
    
  $( [25-Sep-2015] $)
  lem3.2 $p |- `[ p p `] `= `[ `[ `[ p `] `] `[ `[ p `] `] `] $=
    lfp lofdf-encl lofdf-encl lfp lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    lfp lfp lofdf-juxt lofdf-encl lfp lfp lofdf-encl lofdf-encl lfp lofdf-encl
    lofdf-encl lofdf-void lofdf-void lofdf-void lfp lfp lofdf-juxt lofdf-encl
    lfp lofdf-encl lofdf-encl lfp lfp c1.2 lofsym lfp lfp lofdf-encl lofdf-encl
    lofdf-void lfp lofdf-void lofdf-void lfp lfp lofdf-juxt lofdf-encl lfp
    lofdf-encl lofdf-encl lfp lfp c1.2 lofsym lfp lfp lofdf-juxt lofdf-encl
    lofid lofrepbx lofrepbx lofsym $.
    
  $( [25-Sep-2015] $)
  c5.2 $p |- p p `= p $=
    lfp lofdf-encl lofdf-encl lfp lfp lofdf-juxt lfp lfp lofdf-encl lofdf-encl
    lfp lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl
    lfp lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lofdf-void
    lofdf-void lofdf-void lofdf-void lfp lfp lofdf-juxt lfp lofdf-encl lfp
    lofdf-encl c6.2 lfp lfp lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl lfp
    lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-void lfp lofdf-encl
    lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lofdf-void lofdf-void lfp
    lfp lofdf-juxt lfp lem3.2 lofdf-void lfp lofdf-encl lofdf-encl lfp
    lofdf-encl lofdf-juxt lofdf-encl lfp lfp lofdf-juxt lofdf-encl lofdf-void
    lofdf-void lofdf-void lfp lfp lofdf-juxt lfp lofdf-encl lofdf-encl lfp
    lofdf-encl lofdf-juxt lofdf-encl lofdf-void lfp lofdf-encl j1.2 lofsym lfp
    lfp lofdf-juxt c1.2 lofrepbx lofrepbx lofrepbx lfp c1.2 lofeucr $.
    $( [25-Sep-2015] $)

  $( =======================================================================

     System_3

     Deriving C6 from the Robbins equation, demonstrating that a Robbins
     algebra is a Boolean algebra. $)

  $( Basis_3 --------------------------------------------- $)

  $( The more familiar form of the Robbins equation is ((p q) (p (q)))
     ` = p, but for this exercise I'll be using the equivalent form: $)
  robbins $a |- `[ `[ `[ p `] q `] `[ p q `] `] `= q $.

  $( System_3 consequences ------------------------------------ $)
  j1.3 $p |- `[ `[ p `] p `] `= $=
    lfp lofdf-encl lfp lofdf-juxt lofdf-encl lfq lofdf-encl lfp lofdf-juxt
    lofdf-encl lfq lfp lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-encl
    lfq lofdf-encl lfp lofdf-juxt lofdf-encl lfq lfp lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-void lfp lofdf-encl lfp
    lofdf-juxt lfq lofdf-encl lfp lofdf-juxt lofdf-encl lfq lfp lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lofdf-encl lfq lofdf-encl lfp lofdf-juxt
    lofdf-encl lfq lfp lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lfp lofdf-encl lfq lofdf-encl lfp lofdf-juxt lofdf-encl lfq lfp lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lofdf-encl lfp lfq lofdf-encl lfp
    lofdf-juxt lofdf-encl lfq lfp lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    lfp lfq lofdf-encl lfp lofdf-juxt lofdf-encl lfq lfp lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl lfq lofdf-encl lfp lofdf-juxt lofdf-encl lfq lfp
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfp lfq lfp robbins lofsym
    lofbeq lfq lofdf-encl lfp lofdf-juxt lofdf-encl lfq lfp lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lfp lfq lfp robbins lofsym lofquad lofbeq
    lfq lofdf-encl lfp lofdf-juxt lofdf-encl lfq lfp lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-void robbins loftrans $.
    
  $( [8-Dec-2016] $)
  c1.3 $p |- `[ `[ p `] `] `= p $=
    lfp lofdf-encl lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-encl lfp
    lofdf-encl lofdf-encl lfp lfp lfp lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl lofdf-encl lfp lofdf-encl lofdf-encl lfp lofdf-juxt lofdf-encl
    lofdf-encl lofdf-void lofdf-void lfp lofdf-encl lofdf-encl lfp lfp
    lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-encl lfp
    lofdf-juxt lofdf-encl lfp lfp lofdf-encl lofdf-encl lofdf-juxt lfp
    lofdf-encl lofdf-encl lfp lofdf-juxt lfp lfp lofdf-encl lofdf-encl lofcmm
    lofbeq lofbeq lfp lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt
    lofdf-encl lofdf-void lofdf-void lfp lfp lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl lofdf-void lofdf-void lfp lofdf-encl lofdf-encl lfp lofdf-void
    robbins lfp lofdf-encl lfp lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lofdf-void lfp
    lfp lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lofdf-void lofdf-void lfp
    lofdf-encl lofdf-encl lfp lofdf-encl lfp lofdf-encl lofdf-encl lofdf-juxt
    lfp lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt lfp lofdf-encl lfp
    lofdf-encl lofdf-encl lofcmm lofbeq lfp lfp lofdf-encl lofdf-encl robbins
    lofrepbx lofrepbx lofrep lfp lofdf-encl lfp lofdf-juxt lofdf-encl
    lofdf-void lfp lofdf-encl lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-void
    lofdf-void lofdf-void lfp lfp j1.3 lfp lofdf-encl lfp robbins lofrepbx
    lofeucr $.
    
  $( [8-Dec-2016] $)
  c6.3 $p |- `[ `[ p `] `[ q `] `] `[ `[ p `] q `] `= p $=
    lfq lfp lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-juxt lofdf-void
    lofdf-void lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-void
    lfp lfq lfp lofdf-encl lofcmm lfq lofdf-encl lfp lofdf-encl lofdf-juxt lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-void lofdf-void lofdf-void lfq
    lfp lofdf-encl lofdf-juxt lofdf-encl lfp lfq lofdf-encl lfp lofdf-encl
    lofcmm lfq lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lfq lfp
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lofdf-encl lfp
    lfq lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lfq lfp lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lofdf-encl lfq lofdf-encl lfp
    lofdf-encl lofdf-juxt lofdf-encl lfq lfp lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt lfp lofdf-encl lofdf-encl lfq lofdf-encl lfp lofdf-encl
    lofdf-juxt lofdf-encl lfq lfp lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    c1.3 lfq lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lfq lfp lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq lfp
    lofdf-encl robbins lofbeq lofeucr lfp c1.3 loftrans lofrepbx lofrepbx $.
    
  $( [5-Oct-2015] $)
  robblem1.3 $p |- `[ `[ `[ `[ q `] `[ p `] `] `[ q `[ p `] `] `] `]
                   `= `[ `[ p `] `] $=
    lfq lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lfq lfp lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq lfp
    lofdf-encl robbins lofbeq $.
    $( [31-Jan-2017] $)


  $( =======================================================================
     Topics in Laws of Form

     Associativity of logical connectives

     Since LoF lacks the concept of associativity, proving that a model of LoF
     has associative connectives may involve meta-reasoning.  For example, the
     proof of (p V q) V r = p V (q V r) corresponds to the equation p q r = p q
     r, which is easy to prove in LoF!  Under the dual interpretation this also
     proves the associativity of conjunction, but here I will prove that more
     directly.  Since p & q corresponds to ((p)(q)), we need to show that
     ((((p)(q))) (r)) = ((p) (((q)(r)))).  Consider the left side of that
     equation -- it evaluates to ((p)(q)(r)), a form symmetric in the three
     variables: $)
  conj3 $p |- `[ `[ `[ `[ p `] `[ q `] `] `] `[ r `] `]
              `= `[ `[ p `] `[ q `] `[ r `] `] $=
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-encl lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-void lfr lofdf-encl lofdf-void
    lofdf-void lfp lofdf-encl lfq lofdf-encl lofdf-juxt c1.0 lofsubb1 $.
    $( [29-Dec-2016] $)

  $( This shows that a permutation of variables in the LHS leaves the
     result unchanged. Specifically, ((((q)(r))) (p)), which is equal to
     ((p) (((q)(r)))) by commutation, will evaluate to the same form as
     ((((p)(q))) (r)). This completes the proof. I call this meta-reasoning
     because we're using an undefined, intuitive notion of symmetry. Below
     is the full-length formal proof. $)

  $( Associativity of conjunction. $)
  conj-assc $p |- `[ `[ `[ `[ p `] `[ q `] `] `] `[ r `] `]
                  `= `[ `[ p `] `[ `[ `[ q `] `[ r `] `] `] `]
            $=
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-encl lfr
    lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lfr lofdf-encl lofdf-juxt
    lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl
    lfq lofdf-encl lfr lofdf-encl lofdf-juxt lofdf-encl lofdf-encl lofdf-juxt
    lofdf-encl lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-encl
    lfr lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-encl
    lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lfr
    lofdf-encl lofdf-juxt lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt
    lofdf-encl lfp lfq lfr conj3 lfq lofdf-encl lfr lofdf-encl lofdf-juxt
    lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl
    lfr lofdf-encl lofdf-juxt lfp lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl
    lfq lfr lfp conj3 lfq lofdf-encl lfr lofdf-encl lofdf-juxt lfp lofdf-encl
    lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-juxt lfr lofdf-encl
    lofdf-juxt lofdf-void lofdf-void lofdf-void lofdf-void lfq lofdf-encl lfr
    lofdf-encl lofdf-juxt lfp lofdf-encl lofcmm lofsubb1 loftrans lofeuc lfq
    lofdf-encl lfr lofdf-encl lofdf-juxt lofdf-encl lofdf-encl lfp lofdf-encl
    lofdf-juxt lfp lofdf-encl lfq lofdf-encl lfr lofdf-encl lofdf-juxt
    lofdf-encl lofdf-encl lofdf-juxt lfq lofdf-encl lfr lofdf-encl lofdf-juxt
    lofdf-encl lofdf-encl lfp lofdf-encl lofcmm lofbeq loftrans $.
    $( [29-Dec-2016] $)

  $( Now I turn to proving the associativity of the biconditional:  (p<->q)<->r
` = p<->(q<->r). I had earlier taken for granted that p<->q, transcribed as (((p)q) ((q)p)), was equivalent to ((p)(q)) (p q). Here I prove it: $)
  bicond $p |- `[ `[ `[ p `] q `] `[ `[ q `] p `] `]
               `= `[ `[ p `] `[ q `] `] `[ p q `] $=
    lfq lfp lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lfp lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-juxt lofdf-encl
    lfq lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lfq lofdf-juxt
    lofdf-encl lofdf-juxt lfq lfp lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-encl lfq lofdf-juxt lofdf-encl lofdf-void lfq lofdf-encl lfp
    lofdf-juxt lofdf-encl lofdf-void lofdf-void lfq lfp lofdf-encl lofdf-juxt
    lfp lofdf-encl lfq lofdf-juxt lfq lfp lofdf-encl lofcmm lofbeq lofsubb1 lfq
    lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl
    lfp lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfq lfp lofdf-encl
    lofdf-juxt lofdf-encl lfq lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lfq
    lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lofdf-encl lfp lofdf-encl
    lofdf-juxt lofdf-encl lfq lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt
    lfq lfp lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lfp lofdf-juxt
    lofdf-encl lofdf-juxt lfq lofdf-encl lofdf-encl lfq lofdf-void lfp
    lofdf-encl lofdf-void lfq lofdf-encl lfp lofdf-juxt lofdf-encl lfq c1.0
    lofsubb1 lofbeq lofdf-void lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl
    lofdf-void lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl
    lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl
    lfp lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lofdf-encl
    lfp lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lfp lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-encl lofdf-juxt
    lofdf-encl lfp lfq lofdf-juxt lofdf-encl lofdf-juxt lofdf-void lofdf-encl
    lfp lofdf-encl lofdf-juxt lofdf-encl lofdf-void lofdf-encl lfp lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-void lofdf-void lfq lofdf-encl lofdf-encl lfp
    lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lfp lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-void lofdf-void lofdf-void lfp c6.0 lofsubb1 lofdf-void
    lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lofdf-encl
    lfp lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfp
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-void lofdf-encl lfp lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lofdf-void lofdf-encl lfp lofdf-encl
    lofdf-juxt lofdf-encl lofdf-void lofdf-encl lfp lofdf-juxt lofdf-encl
    lofdf-juxt lfq lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt lfq lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lfq lofdf-juxt
    lofdf-encl lofdf-juxt lfq lofdf-encl lofdf-encl lfp lofdf-encl lofdf-juxt
    lofdf-encl lfq lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt lofdf-void
    lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-void lofdf-encl lfp lofdf-encl
    lofdf-juxt lofdf-encl lofdf-void lofdf-void lofdf-void lofdf-void lofcmmbx
    lfp lofdf-void lfq lofdf-encl lfq lofdf-void c9.0 lofeucr lofeucr lofeucr
    lofeucr $.
    $( [29-Dec-2016] $)

  $( Next I'll need the following two lemmas: $)
  c2lem1 $p |- `[ q `[ p q `] r `] `= `[ `[ p `] q r `] $=
    lfq lfp lfq lofdf-juxt lofdf-encl lofdf-juxt lfr lofdf-juxt lfp lofdf-encl
    lfq lofdf-juxt lfr lofdf-juxt lfq lfp lfq lofdf-juxt lofdf-encl lofdf-juxt
    lfr lofdf-juxt lfp lfq lofdf-juxt lofdf-encl lfq lofdf-juxt lfr lofdf-juxt
    lfp lofdf-encl lfq lofdf-juxt lfr lofdf-juxt lfq lfp lfq lofdf-juxt
    lofdf-encl lofdf-void lofdf-void lfr lofcmmx lfp lfq lofdf-juxt lofdf-encl
    lfq lofdf-juxt lfp lofdf-encl lfq lofdf-juxt lfr lfp lfq c2.0 lofsub
    loftrans lofbeq $.
    
  $( [29-Dec-2016] $)
  c2lem2 $p |- `[ p `[ p q `] r `] `= `[ p `[ q `] r `] $=
    lfp lfp lfq lofdf-juxt lofdf-encl lofdf-juxt lfr lofdf-juxt lfp lfq
    lofdf-encl lofdf-juxt lfr lofdf-juxt lfp lfp lfq lofdf-juxt lofdf-encl
    lofdf-juxt lfr lofdf-juxt lfq lofdf-encl lfp lofdf-juxt lfr lofdf-juxt lfp
    lfq lofdf-encl lofdf-juxt lfr lofdf-juxt lfp lfp lfq lofdf-juxt lofdf-encl
    lofdf-juxt lfr lofdf-juxt lfq lfp lofdf-juxt lofdf-encl lfp lofdf-juxt lfr
    lofdf-juxt lfq lofdf-encl lfp lofdf-juxt lfr lofdf-juxt lfp lfp lfq
    lofdf-juxt lofdf-encl lofdf-juxt lfr lofdf-juxt lfp lfq lfp lofdf-juxt
    lofdf-encl lofdf-juxt lfr lofdf-juxt lfq lfp lofdf-juxt lofdf-encl lfp
    lofdf-juxt lfr lofdf-juxt lfp lfq lofdf-void lofdf-void lofdf-void lfp lfr
    lofcmmbx lfp lfq lfp lofdf-juxt lofdf-encl lofdf-void lofdf-void lfr
    lofcmmx loftrans lfq lfp lofdf-juxt lofdf-encl lfp lofdf-juxt lfq
    lofdf-encl lfp lofdf-juxt lfr lfq lfp c2.0 lofsub loftrans lfq lofdf-encl
    lfp lofdf-void lofdf-void lfr lofcmmx loftrans lofbeq $.
    $( [29-Dec-2016] $)

  $( Let A
` = p<->q <-> ((p)(q)) (p q) and B <-> q<->r <-> ((q)(r)) (q r). Proving that the biconditional associates amounts to proving: ((A)(r)) (A r) = ((p)(B)) (p B), i.e., ((((p)(q)) (p q))(r)) (((p)(q)) (p q) r) = ((p)(((q)(r)) (q r))) (p ((q)(r)) (q r)). Consider the left side of that equation -- as in the case of conjunction, it evaluates to a form symmetric in the three variables: $)
  bic3 $p |- `[ `[ `[ `[ p `] `[ q `] `] `[ p q `] `] `[ r `] `]
             `[ `[ `[ p `] `[ q `] `] `[ p q `] r `]
             `= `[ `[ p `] `[ q `] `[ r `] `] `[ p q `[ r `] `]
                 `[ p `[ q `] r `] `[ `[ p `] q r `] $=
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lfq lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lfr lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lfq lofdf-juxt
    lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl
    lfq lofdf-encl lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lfp lfq
    lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp lfq
    lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt lfq lfp lfq
    lofdf-juxt lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl
    lfp lfq lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp lfq
    lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl
    lfq lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq
    lofdf-encl lofdf-juxt lofdf-encl lfp lfq lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lfr lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-encl lofdf-juxt lofdf-encl lfp lfq lofdf-juxt lofdf-encl lofdf-juxt
    lfr lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl
    lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lfp lfq lofdf-juxt lfr
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp lfp lfq lofdf-juxt
    lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lfq lfp lfq lofdf-juxt
    lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt lofdf-juxt lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl
    lfp lfq lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp lfq
    lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lfq lfp lfq lofdf-juxt
    lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt lofdf-juxt lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lfq lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lfr lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl
    lfp lfq lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lfq lofdf-juxt
    lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lfp lfp lfq lofdf-juxt
    lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lfq lfp lfq lofdf-juxt
    lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl
    lfq lofdf-encl lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lfp lfq
    lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    lofdf-encl lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lfq
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfr lofdf-encl lofdf-juxt
    lofdf-encl lfp lofdf-encl lfq lofdf-encl lofdf-juxt lfr lofdf-encl
    lofdf-juxt lofdf-encl lfp lfq lofdf-juxt lfr lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-juxt lfr
    lofdf-encl lofdf-juxt lofdf-encl lfp lfq lofdf-juxt lfr lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-encl
    lofdf-juxt lofdf-encl lfp lfq lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    lfr lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-juxt lfp lfq
    lofdf-juxt lfr lofdf-encl j2.0 lofbeq lfp lofdf-encl lfq lofdf-encl
    lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lfp lfq lofdf-juxt lfr
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt c1.0 lofeucr lfp lfp lfq
    lofdf-juxt lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lfq lfp lfq
    lofdf-juxt lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lofdf-encl lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl
    lfp lfq lofdf-juxt lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lfp lfp
    lfq lofdf-juxt lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lfq lfp lfq
    lofdf-juxt lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt lfp
    lfp lfq lofdf-juxt lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lfq lfp
    lfq lofdf-juxt lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lfq
    lofdf-juxt lofdf-encl lofdf-juxt lfr lofdf-juxt lfp lfq lfp lfq lofdf-juxt
    lofdf-encl lfr lofdf-juxt j2.0 lofbeq lfp lfp lfq lofdf-juxt lofdf-encl
    lofdf-juxt lfr lofdf-juxt lofdf-encl lfq lfp lfq lofdf-juxt lofdf-encl
    lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt c1.0 lofeucr lofquad lfp
    lfp lfq lofdf-juxt lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lfp lfq
    lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-encl lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lfp lfq
    lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfq lfp lfq
    lofdf-juxt lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lfp lfq lfr
    c2lem2 lofsubst loftrans lfq lfp lfq lofdf-juxt lofdf-encl lofdf-juxt lfr
    lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-juxt lfr lofdf-juxt
    lofdf-encl lfp lofdf-encl lfq lofdf-encl lofdf-juxt lfr lofdf-encl
    lofdf-juxt lofdf-encl lfp lfq lofdf-juxt lfr lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt lfp lfq lofdf-encl lofdf-juxt lfr lofdf-juxt
    lofdf-encl lofdf-juxt lfp lfq lfr c2lem1 lofsubr loftrans $.
    $( [29-Dec-2016] $)

  $( This completes the informal proof that the biconditional associates.
     Below is the formal proof.  First, we need a permuted version of bic3. $)
  bic3x $p |- `[ `[ `[ `[ q `] `[ r `] `] `[ q r `] `] `[ p `] `]
              `[ `[ `[ q `] `[ r `] `] `[ q r `] p `]
              `= `[ `[ p `] `[ q `] `[ r `] `] `[ p q `[ r `] `]
                  `[ p `[ q `] r `] `[ `[ p `] q r `] $=
    lfq lofdf-encl lfr lofdf-encl lofdf-juxt lofdf-encl lfq lfr lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lfq
    lofdf-encl lfr lofdf-encl lofdf-juxt lofdf-encl lfq lfr lofdf-juxt
    lofdf-encl lofdf-juxt lfp lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl
    lfq lofdf-encl lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-encl lfq lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt lfp lfq
    lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt lfp lfq
    lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl
    lfq lofdf-encl lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lfp lfq
    lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp lfq
    lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl
    lfq lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfr
    lofdf-encl lofdf-juxt lofdf-encl lfq lfr lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lfr
    lofdf-encl lofdf-juxt lofdf-encl lfq lfr lofdf-juxt lofdf-encl lofdf-juxt
    lfp lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl
    lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt lfp lfq lofdf-juxt lfr
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp lfq lofdf-encl lofdf-juxt
    lfr lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl
    lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt lfp lfq lofdf-encl
    lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt lfp lfq lofdf-juxt lfr
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfr lofdf-encl
    lofdf-juxt lofdf-encl lfq lfr lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    lfp lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lfr lofdf-encl
    lofdf-juxt lofdf-encl lfq lfr lofdf-juxt lofdf-encl lofdf-juxt lfp
    lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-juxt
    lfr lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-juxt lfr
    lofdf-juxt lofdf-encl lofdf-juxt lfp lfq lofdf-juxt lfr lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfr lofdf-juxt lfp
    lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-juxt
    lfr lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-juxt lfr
    lofdf-juxt lofdf-encl lofdf-juxt lfp lfq lofdf-juxt lfr lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lfp lfq lofdf-encl lofdf-juxt lfr
    lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfr lofdf-encl lofdf-juxt
    lofdf-encl lfq lfr lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lfr lofdf-encl lofdf-juxt
    lofdf-encl lfq lfr lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-juxt
    lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-juxt lfr
    lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-juxt lfr
    lofdf-juxt lofdf-encl lofdf-juxt lfq lfr lofdf-encl lofdf-juxt lfp
    lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfr lofdf-juxt lfp
    lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-juxt
    lfr lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-juxt lfr
    lofdf-juxt lofdf-encl lofdf-juxt lfp lfq lofdf-juxt lfr lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfr lofdf-juxt lfp
    lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfr lofdf-encl lofdf-juxt
    lofdf-encl lfq lfr lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lfr lofdf-encl lofdf-juxt
    lofdf-encl lfq lfr lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-juxt
    lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-juxt lfr
    lofdf-encl lofdf-juxt lofdf-encl lfq lfr lofdf-juxt lfp lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lfq lfr lofdf-encl lofdf-juxt lfp
    lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfr lofdf-juxt lfp
    lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-juxt
    lfr lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-juxt lfr
    lofdf-juxt lofdf-encl lofdf-juxt lfq lfr lofdf-encl lofdf-juxt lfp
    lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfr lofdf-juxt lfp
    lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfr lofdf-encl lofdf-juxt
    lofdf-encl lfq lfr lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lfr lofdf-encl lofdf-juxt
    lofdf-encl lfq lfr lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-juxt
    lofdf-encl lofdf-juxt lfq lofdf-encl lfr lofdf-encl lofdf-juxt lfp
    lofdf-encl lofdf-juxt lofdf-encl lfq lfr lofdf-juxt lfp lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lfq lfr lofdf-encl lofdf-juxt lfp
    lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfr lofdf-juxt lfp
    lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-juxt
    lfr lofdf-encl lofdf-juxt lofdf-encl lfq lfr lofdf-juxt lfp lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lfq lfr lofdf-encl lofdf-juxt lfp
    lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfr lofdf-juxt lfp
    lofdf-juxt lofdf-encl lofdf-juxt lfq lfr lfp bic3 lfq lofdf-encl lfr
    lofdf-encl lofdf-juxt lfp lofdf-encl lofdf-void lofdf-void lofdf-void
    lofdf-void lfq lfr lofdf-juxt lfp lofdf-encl lofdf-juxt lofdf-encl lfq lfr
    lofdf-encl lofdf-juxt lfp lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl
    lfr lofdf-juxt lfp lofdf-juxt lofdf-encl lofdf-juxt lofcmmbx loftrans lfq
    lfr lofdf-juxt lfp lofdf-encl lofdf-void lofdf-void lofdf-void lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl
    lfq lfr lofdf-encl lofdf-juxt lfp lofdf-juxt lofdf-encl lfq lofdf-encl lfr
    lofdf-juxt lfp lofdf-juxt lofdf-encl lofdf-juxt lofcmmbx loftrans lfq lfr
    lofdf-encl lofdf-juxt lfp lofdf-void lofdf-void lofdf-void lfp lofdf-encl
    lfq lofdf-encl lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-encl lfq lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt lfq
    lofdf-encl lfr lofdf-juxt lfp lofdf-juxt lofdf-encl lofcmmbx loftrans lfq
    lofdf-encl lfr lofdf-juxt lfp lofdf-void lofdf-void lofdf-void lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl
    lfp lofdf-encl lfq lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt lfp lfq
    lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-void
    lofcmmbx loftrans lfp lfq lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl
    lfp lfq lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-encl lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl
    lfq lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt lofdf-void lofdf-void
    lofcmmx loftrans lfp lofdf-encl lfq lofdf-juxt lfr lofdf-juxt lofdf-encl
    lfp lfq lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq
    lofdf-encl lofdf-juxt lfr lofdf-encl lofdf-juxt lofdf-encl lfp lfq
    lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-void lofcmmx loftrans
    $.
    $( [29-Dec-2016] $)

  $( The associativity of the biconditional. $)
  bicond-assc $p |- `[ `[ `[ `[ p `] `[ q `] `] `[ p q `] `] `[ r `] `]
                    `[ `[ `[ p `] `[ q `] `] `[ p q `] r `]
                    `= `[ `[ p `] `[ `[ `[ q `] `[ r `] `] `[ q r `] `] `]
                        `[ p `[ `[ q `] `[ r `] `] `[ q r `] `] $=
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lfq lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lfr lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfp lfq lofdf-juxt
    lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl
    lfr lofdf-encl lofdf-juxt lofdf-encl lfq lfr lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl
    lfr lofdf-encl lofdf-juxt lofdf-encl lfq lfr lofdf-juxt lofdf-encl
    lofdf-juxt lfp lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq
    lofdf-encl lfr lofdf-encl lofdf-juxt lofdf-encl lfq lfr lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfp lfq lofdf-encl
    lfr lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfq lfr lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl
    lofdf-juxt lofdf-encl lfp lfq lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    lfr lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lfq lofdf-encl
    lofdf-juxt lofdf-encl lfp lfq lofdf-juxt lofdf-encl lofdf-juxt lfr
    lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl lofdf-juxt
    lfr lofdf-encl lofdf-juxt lofdf-encl lfp lfq lofdf-juxt lfr lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lfp lfq lofdf-encl lofdf-juxt lfr
    lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-juxt lfr
    lofdf-juxt lofdf-encl lofdf-juxt lfq lofdf-encl lfr lofdf-encl lofdf-juxt
    lofdf-encl lfq lfr lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lfr lofdf-encl lofdf-juxt
    lofdf-encl lfq lfr lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-juxt
    lofdf-encl lofdf-juxt lfp lfq lfr bic3 lfp lfq lfr bic3x lofeuc lfq
    lofdf-encl lfr lofdf-encl lofdf-juxt lofdf-encl lfq lfr lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl lfq
    lofdf-encl lfr lofdf-encl lofdf-juxt lofdf-encl lfq lfr lofdf-juxt
    lofdf-encl lofdf-juxt lfp lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl
    lfq lofdf-encl lfr lofdf-encl lofdf-juxt lofdf-encl lfq lfr lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfq lofdf-encl lfr
    lofdf-encl lofdf-juxt lofdf-encl lfq lfr lofdf-juxt lofdf-encl lofdf-juxt
    lfp lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lfq lofdf-encl lfr
    lofdf-encl lofdf-juxt lofdf-encl lfq lfr lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt lofdf-encl lfp lfq lofdf-encl lfr lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lfq lfr lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt lfq lofdf-encl lfr lofdf-encl lofdf-juxt lofdf-encl
    lfq lfr lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-encl
    lofdf-void lofdf-void lofdf-void lofdf-void lfq lofdf-encl lfr lofdf-encl
    lofdf-juxt lofdf-encl lfq lfr lofdf-juxt lofdf-encl lofdf-juxt lfp
    lofdf-juxt lofdf-encl lofcmmbx lfq lofdf-encl lfr lofdf-encl lofdf-juxt
    lofdf-encl lfq lfr lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-void
    lofdf-void lofdf-void lfp lofdf-encl lfq lofdf-encl lfr lofdf-encl
    lofdf-juxt lofdf-encl lfq lfr lofdf-juxt lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt lofdf-encl lofdf-void lofcmmbx loftrans loftrans $.
    $( [29-Dec-2016] $)



  
  
  $( Versions of C1. $)

  lofc1r $p |- p `= `[ `[ p `] `] $=
    lfp lofdf-encl lofdf-encl  lfp
    lfp c1.0 lofsym  $.

  lofc1x $p |- u `[ `[ p `] `] v `= u p v $=
    lfp lofdf-encl lofdf-encl  lfp
    lfu lfv
    lfp c1.0 
    lofsubst  $.

  lofc1rx $p |-  u p v `=  u `[ `[ p `] `] v  $=
    lfp  lfp lofdf-encl lofdf-encl
    lfu lfv
    lfp lofc1r
    lofsubst   $.

  lofc1bx $p |- w `[ u `[ `[ p `] `] v `] x `= w `[ u p v `] x $=
    lfu lfp lofdf-encl lofdf-encl lofdf-juxt lfv lofdf-juxt
    lfu lfp lofdf-juxt lfv lofdf-juxt
    lofdf-void lofdf-void
    lfw lfx
    lfp lfu lfv lofc1x
    lofsubb1  $.

  lofc1rbx $p |- w `[ u p v `] x `=  w `[ u `[ `[ p `] `] v `] x  $=
    lfw lfu lfp lofdf-encl lofdf-encl lofdf-juxt lfv lofdf-juxt lofdf-encl
    lofdf-juxt lfx lofdf-juxt
    lfw lfu lfp lofdf-juxt lfv lofdf-juxt lofdf-encl lofdf-juxt lfx lofdf-juxt
    lfp lfu lfv lfw lfx  lofc1bx lofsym  $.
  
  $( Versions of C2. $)
  lofc2x $p |- u `[ p q v `] w q x `= u `[ p v `] w q x $= 

    lfu lfp lfv lofdf-juxt lofdf-encl lofdf-juxt lfw
    lofdf-juxt lfq lofdf-juxt lfx lofdf-juxt

    lfu lfp lfq lofdf-juxt lfv lofdf-juxt lofdf-encl lofdf-juxt lfw
    lofdf-juxt lfq lofdf-juxt lfx lofdf-juxt

    lfq lfw lofdf-juxt
    lfw lfq lofdf-juxt
    lfu lfp lfv lofdf-juxt lofdf-encl lofdf-juxt
    lfx
    lfu lfp lfq lofdf-juxt lfv lofdf-juxt lofdf-encl lofdf-juxt lfw
    lofdf-juxt lfq lofdf-juxt lfx lofdf-juxt

    lfq lfw lofcmm
    
    lfp lfv lofdf-juxt lfq lofdf-juxt lofdf-encl lfq lofdf-juxt
    lfp lfv lofdf-juxt lofdf-encl lfq lofdf-juxt
    lfu
    lfw lfx lofdf-juxt
    lfu lfp lfq lofdf-juxt lfv lofdf-juxt lofdf-encl lofdf-juxt lfw
    lofdf-juxt lfq lofdf-juxt lfx lofdf-juxt

    lfp lfv lofdf-juxt   lfq
    c2.0

    lfu lfp lfq lofdf-juxt lfv lofdf-juxt lofdf-encl lofdf-juxt lfw
    lofdf-juxt lfq lofdf-juxt lfx lofdf-juxt

    lfu lfp lfv lofdf-juxt lfq lofdf-juxt lofdf-encl lofdf-juxt lfq
    lofdf-juxt lfw lofdf-juxt lfx lofdf-juxt

    lfu lfp lfq lofdf-juxt lfv lofdf-juxt lofdf-encl lofdf-juxt lfw
    lofdf-juxt lfq lofdf-juxt lfx lofdf-juxt

    lfu lfp lfv lofdf-juxt lfq lofdf-juxt lofdf-encl lofdf-juxt lfw
    lofdf-juxt lfq lofdf-juxt lfx lofdf-juxt

    lfu lfp lfv lofdf-juxt lfq lofdf-juxt lofdf-encl lofdf-juxt lfq
    lofdf-juxt lfw lofdf-juxt lfx lofdf-juxt

    lfq lfv lfp lofdf-void lofdf-void lfu lfw lfq lofdf-juxt lfx lofdf-juxt
    lofcmmbx
    
    lfw lfq   lfu lfp lfv lofdf-juxt lfq lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-void lfx
    lofcmmx
    loftrans
    lofsym

    lofrep
    lofrep
    lofsym
    $.

  lofc2bx $p |- y `[ u `[ p q v `] w q x `] z `= y `[ u `[ p v `] w q x `] z $=
    lfu lfp lfq lofdf-juxt lfv lofdf-juxt lofdf-encl lofdf-juxt
    lfw lofdf-juxt lfq lofdf-juxt lfx lofdf-juxt
    lfu lfp lfv lofdf-juxt lofdf-encl lofdf-juxt
    lfw lofdf-juxt lfq lofdf-juxt lfx lofdf-juxt
    lofdf-void lofdf-void lfy lfz
    lfp lfq lfu lfv lfw lfx
    lofc2x
    lofsubb1 $.

  lofc2rx $p |-  u q v `[ p q w `] x `= u q v `[ p w `] x $=
       
    lfu lfq lofdf-juxt lfv lofdf-juxt  lfp lfq lofdf-juxt lfw lofdf-juxt
    lofdf-encl lofdf-juxt lfx lofdf-juxt

    lfu lfp  lfw lofdf-juxt lofdf-encl lofdf-juxt
    lfq lofdf-juxt lfv lofdf-juxt lfx lofdf-juxt

    lfu lfq lofdf-juxt lfv lofdf-juxt  lfp  lfw lofdf-juxt
    lofdf-encl lofdf-juxt lfx lofdf-juxt

    lfu lfq lofdf-juxt lfv lofdf-juxt  lfp lfq lofdf-juxt lfw lofdf-juxt
    lofdf-encl lofdf-juxt lfx lofdf-juxt

    lfu lfp lfq lofdf-juxt lfw lofdf-juxt lofdf-encl lofdf-juxt
    lfq lofdf-juxt lfv lofdf-juxt lfx lofdf-juxt

    lfu lfp  lfw lofdf-juxt lofdf-encl lofdf-juxt
    lfq lofdf-juxt lfv lofdf-juxt lfx lofdf-juxt

    lfq lfv lofdf-juxt
    lfp lfq lofdf-juxt lfw lofdf-juxt lofdf-encl
    lfu
    lofdf-void
    lfx
    lofcmmx   
    
    lfp lfq lfu lfw lofdf-void lfv lfx lofdf-juxt
    lofc2x
    loftrans
    
    lfp lfw lofdf-juxt lofdf-encl
    lfq lfv lofdf-juxt
    lfu
    lofdf-void
    lfx
    lofcmmx
    loftrans
     $.

  lofc2rbx $p |- y `[ u `[ p v `] w q x `] z `= y `[ u `[ p q v `] w q x `] z $=
    lfy lfu lfp lfq lofdf-juxt lfv lofdf-juxt lofdf-encl lofdf-juxt
    lfw lofdf-juxt lfq lofdf-juxt lfx lofdf-juxt lofdf-encl lofdf-juxt
    lfz lofdf-juxt
    lfy lfu lfp lfv lofdf-juxt lofdf-encl lofdf-juxt
    lfw lofdf-juxt lfq lofdf-juxt lfx lofdf-juxt lofdf-encl lofdf-juxt
    lfz lofdf-juxt
    lfp lfq lfu lfv lfw lfx lfy lfz
    lofc2bx
    lofsym $.

  lofc2e $p |-  u `[ p `] v p w `=  `[ `]  $=

    lfu lfp lofdf-encl lofdf-juxt lfv lofdf-juxt lfp lofdf-juxt lfw lofdf-juxt
    lfu lofdf-void lofdf-encl lofdf-juxt lfv lofdf-juxt lfp lofdf-juxt lfw lofdf-juxt
    lofdf-void lofdf-encl

    lofdf-void lfp lfu lofdf-void lfv lfw
    lofc2x
    
    lfu lofdf-void lofdf-encl lofdf-juxt lfv lofdf-juxt lfp lofdf-juxt lfw lofdf-juxt
    lofdf-void lofdf-encl lfu lofdf-juxt lfv lofdf-juxt lfp lofdf-juxt lfw lofdf-juxt
    lofdf-void lofdf-encl
    lfu lofdf-void lofdf-encl lofdf-void lofdf-void
    lfv lfp lofdf-juxt lfw lofdf-juxt
    lofcmmx
    lfu lfv lofdf-juxt lfp lofdf-juxt lfw lofdf-juxt
    c3.0
    loftrans
    loftrans
    $.
  
  $( Versions of C3. $)
  lofc3x $p |- p `[ `] q `= `[ `]  $= 
    lfp lofdf-void lofdf-encl lofdf-juxt lfq lofdf-juxt
    lofdf-void lofdf-encl lfq lofdf-juxt lfp lofdf-juxt
    lofdf-void lofdf-encl

    lfp lofdf-void lofdf-encl lfq lofdf-juxt lofcmm 
    lfq lfp lofdf-juxt c3.0

    loftrans
    $.

  lofc3bx $p |- u `[ p `[ `] q `] v `= u v  $=
    
    lfu lfp lofdf-void lofdf-encl lofdf-juxt lfq lofdf-juxt lofdf-encl
    lofdf-juxt lfv lofdf-juxt
    lfu lofdf-void lofdf-encl lofdf-encl lofdf-juxt lfv lofdf-juxt
    lfu lfv lofdf-juxt
    
    lfp lofdf-void lofdf-encl lofdf-juxt lfq lofdf-juxt
    lofdf-void lofdf-encl
    lofdf-void lofdf-void lfu lfv
    lfp lfq
    lofc3x
    lofsubb1

    lofdf-void lfu lfv
    lofc1x
    loftrans 
    $.

  $( Versions of C4. $)
  lofc4x $p |- w `[ u `[ p `] v `] x p y `= w p x y $=

    lfw lfu lfp lofdf-encl lofdf-juxt lfv lofdf-juxt lofdf-encl lofdf-juxt
    lfx lofdf-juxt lfp lofdf-juxt lfy lofdf-juxt

    lfw lfp lofdf-encl lfu lofdf-juxt lfv lofdf-juxt lofdf-encl lofdf-juxt
    lfp lofdf-juxt lfx lofdf-juxt lfy lofdf-juxt

    lfw lfp lofdf-juxt lfx lofdf-juxt lfy lofdf-juxt

    
    lfw lfu lfp lofdf-encl lofdf-juxt lfv lofdf-juxt lofdf-encl lofdf-juxt
    lfx lofdf-juxt lfp lofdf-juxt lfy lofdf-juxt

    lfw lfp lofdf-encl lfu lofdf-juxt lfv lofdf-juxt lofdf-encl lofdf-juxt
    lfx lofdf-juxt lfp lofdf-juxt lfy lofdf-juxt

    lfw lfp lofdf-encl lfu lofdf-juxt lfv lofdf-juxt lofdf-encl lofdf-juxt
    lfp lofdf-juxt lfx lofdf-juxt lfy lofdf-juxt

    lfu lfp lofdf-encl lofdf-void lofdf-void lfv lfw
    lfx lfp lofdf-juxt lfy lofdf-juxt
    lofcmmbx  
    
    lfx lfp
    lfw lfp lofdf-encl lfu lofdf-juxt lfv lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-void lfy
    lofcmmx
    loftrans
    
    lfp lofdf-encl lfu lofdf-juxt lfv lofdf-juxt lofdf-encl lfp lofdf-juxt
    lfp
    lfw
    lfx lfy lofdf-juxt
    lfw lfp lofdf-encl lfu lofdf-juxt lfv lofdf-juxt lofdf-encl lofdf-juxt
    lfp lofdf-juxt lfx lofdf-juxt lfy lofdf-juxt

    lfp lfu lfv lofdf-juxt c4.0

    lfw lfp lofdf-encl lfu lofdf-juxt lfv lofdf-juxt lofdf-encl lofdf-juxt
    lfp lofdf-juxt lfx lofdf-juxt lfy lofdf-juxt
    lofid

    lofrep
    lofeuc
    $.

  lofc4rx $p |- w p x y `= w `[ u `[ p `] v `] x p y $=
    lfw lfu lfp lofdf-encl lofdf-juxt lfv lofdf-juxt lofdf-encl lofdf-juxt
    lfx lofdf-juxt lfp lofdf-juxt lfy lofdf-juxt
    lfw lfp lofdf-juxt lfx lofdf-juxt lfy lofdf-juxt
    lfp lfu lfv lfw lfx lfy
    lofc4x
    lofsym
    $.

  $( Versions of C5. $)
  lofc5x $p |- u p v p w `= u p v w  $=
                
    lfu lfp lofdf-juxt lfv lofdf-juxt lfp lofdf-juxt lfw lofdf-juxt
    lfu lfp lofdf-juxt lfp lofdf-juxt lfv lofdf-juxt lfw lofdf-juxt
    lfu lfp lofdf-juxt lfv lofdf-juxt lfw lofdf-juxt

    lfv lfp lfu lfp lofdf-juxt lofdf-void lfw
    lofcmmx

    lfp lfp lofdf-juxt   lfp
    lfu   lfv lfw lofdf-juxt
    lfu lfp lofdf-juxt lfp lofdf-juxt lfv lofdf-juxt lfw lofdf-juxt
    lfp c5.0
    lfu lfp lofdf-juxt lfp lofdf-juxt lfv lofdf-juxt lfw lofdf-juxt
    lofid
    lofrep
    lofeuc
    $.

  lofc5rx $p |- u p v w `= u p v p w $=
    lfu lfp lofdf-juxt lfv lofdf-juxt lfp lofdf-juxt lfw lofdf-juxt
    lfu lfp lofdf-juxt lfv lofdf-juxt lfw lofdf-juxt
    lfp lfu lfv lfw  lofc5x
    lofsym
    $.

  $( Versions of J1. $)
  lofj1x $p |-   x `[ u `[ p `] v p w `] y `= x y $=
                 
    lfx lfu lfp lofdf-encl lofdf-juxt lfv lofdf-juxt lfp lofdf-juxt
    lfw lofdf-juxt lofdf-encl lofdf-juxt lfy lofdf-juxt
    lfx lfu lofdf-void lofdf-encl lofdf-juxt lfv lofdf-juxt lfp lofdf-juxt
    lfw lofdf-juxt lofdf-encl lofdf-juxt lfy lofdf-juxt
    lfx lfy lofdf-juxt

    lofdf-void lfp lfu lofdf-void lfv lfw lfx lfy
    lofc2bx
    
    lfu lfv lfp lofdf-juxt lfw lofdf-juxt lfx lfy
    lofc3bx
    loftrans
    $.

  lofj1rx $p |- x y `= x `[ u `[ p `] v p w `] y $=
    lfx lfu lfp lofdf-encl lofdf-juxt lfv lofdf-juxt lfp lofdf-juxt
    lfw lofdf-juxt lofdf-encl lofdf-juxt lfy lofdf-juxt
    lfx lfy lofdf-juxt
    lfp lfu lfv lfw lfx lfy 
    lofj1x
    lofsym
    $.

  $( Versions of J2. $)
  lofj2x $p |- u `[ `[ p r `] `[ q r `] `] v w
              `= u `[ `[ p `] `[ q `] `] v r w $=    

    lfu lfp lfr lofdf-juxt lofdf-encl lfq lfr lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt lfv lofdf-juxt lfw lofdf-juxt
    lfu lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lfr lofdf-juxt lfv lofdf-juxt lfw lofdf-juxt
    lfu lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lfv lofdf-juxt lfr lofdf-juxt lfw lofdf-juxt

    lfp lfr lofdf-juxt lofdf-encl lfq lfr lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lfr lofdf-juxt
    lfu lfv lfw lofdf-juxt
    lfp lfq lfr          
    j2.0
    lofsubst
    
    lfr lfv
    lfu lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-void
    lfw
    lofcmmx
    loftrans
    $.

  lofj2rx $p |- u `[ `[ p `] `[ q `] `] v r w
                `= u `[ `[ p r `] `[ q r `] `] v w $=
    
    lfu lfp lfr lofdf-juxt lofdf-encl lfq lfr lofdf-juxt lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt lfv lofdf-juxt lfw lofdf-juxt
    lfu lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lfv lofdf-juxt lfr lofdf-juxt lfw lofdf-juxt
    
    lfp lfq lfr lfu lfv lfw
    lofj2x
    lofsym
    $.

    $( ---------------- MIXED THEOREMS ----------------- $)
  lofelimeq $p |- `[ `[ p `] `[ `[ `] `] `] `[ p `[ `] `] `= p $=
    lfp lofdf-encl lofdf-void lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-void lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-void
    lofdf-encl lofdf-encl lfp lofdf-juxt lfp lfp lofdf-encl lofdf-void
    lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-void lofdf-encl
    lofdf-juxt lofdf-encl lofdf-juxt lofdf-void lofdf-encl lfp lofdf-juxt
    lofdf-encl lfp lofdf-juxt lofdf-void lofdf-encl lofdf-encl lfp lofdf-juxt
    lfp lofdf-encl lofdf-void lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-void lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-void
    lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt lofdf-void lofdf-encl lfp
    lofdf-juxt lofdf-encl lfp lofdf-juxt lfp lofdf-encl lofdf-void lofdf-encl
    lofdf-encl lofdf-juxt lofdf-encl lfp lofdf-void lofdf-encl lofdf-juxt
    lofdf-encl lofdf-juxt lfp lfp lofdf-void lofdf-encl lofdf-juxt lofdf-encl
    lofdf-juxt lfp lofdf-void lofdf-encl lfp lofdf-juxt lofdf-encl lofdf-juxt
    lfp lofdf-encl lofdf-void lofdf-encl lofdf-encl lofdf-juxt lofdf-encl lfp
    lofdf-void lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl
    lofdf-encl lfp lofdf-void lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lfp
    lfp lofdf-void lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt lofdf-void
    lofdf-encl lofdf-encl lofdf-void lfp lofdf-encl lofdf-void lofdf-void lfp
    lofdf-void lofdf-encl lofdf-juxt lofdf-encl i2.1 lofsubb1 lfp lofdf-encl
    lofdf-encl lfp lofdf-void lfp lofdf-void lofdf-encl lofdf-juxt lofdf-encl
    lfp c1.0 lofsubst loftrans lfp lofdf-void lofdf-encl lofdf-void lofdf-void
    lofdf-void lfp lofdf-void lofcmmbx loftrans lfp lofdf-void lofdf-encl lfp
    lofdf-juxt lofdf-encl lofcmm loftrans lofdf-void lofdf-encl lfp c2.0
    loftrans lofdf-void lofdf-encl lofdf-encl lofdf-void lofdf-void lfp i2.1
    lofsubst loftrans $.
    $( [29-Jan-2017] $)


  $( LoF Deduction Theorems $)

  ${
    lofax-ded.1 $e |- p `= q $.
    lofax-ded.2 $e |- p $.
    lofax-ded   $a |- q $.
  $}

  ${
    lofelim.1 $e |- p `= `[ `] $.
    $( If ` p ` equals the marked state (i.e., truth), we can assert ` p ` . $)
    lofelim   $p |- p $=
    lfp lofdf-encl lofdf-void lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    lfp lofdf-void lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lfp
    lfp lofelimeq
    lfp lofdf-void lofdf-encl
    lofelim.1
    lofdf-NtoU
    lofax-ded
    $.
  $}

  ${
    lofintr.1 $e |- p $.
    $( If we can assert ` p ` , then we can assert ` p `= `[ `] ` 
       (i.e., ` p ` is true). $)
    lofintr   $p |- p `= `[ `]  $=
    lfp lofdf-void lofdf-encl
    lfp
    lfp lofdf-encl lofdf-void lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    lfp lofdf-void lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lfp lofdf-encl lofdf-void lofdf-encl lofdf-encl lofdf-juxt lofdf-encl
    lfp lofdf-void lofdf-encl lofdf-juxt lofdf-encl lofdf-juxt
    lfp
    lfp lofelimeq lofsym
    lofintr.1
    lofax-ded
    lofdf-UtoN
    $.
  $}

  ${
    lofeucrelim.1 $e |- p `= q $.
    lofeucrelim.2 $e |- p `= `[ `] $.
    lofeucrelim   $p |- q $=
      lfq
      lfp lfq lofdf-void lofdf-encl
      lofeucrelim.1 lofeucrelim.2 lofeucr
      lofelim
    $.
  $}

  ${
    loftranselim.1 $e |- p `= q $.
    loftranselim.2 $e |- q `= `[ `] $.
    loftranselim   $p |- p $=
      lfp
      lfp lfq lofdf-void lofdf-encl
      loftranselim.1 loftranselim.2 loftrans
      lofelim
    $.
  $}  

  ${
    lofand.1 $e |- p $.
    lofand.2 $e |- q $.
    lofand   $p |- `[ `[ p `] `[ q `] `] $=

    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl

    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl
    lofdf-void lofdf-encl lfq lofdf-juxt lofdf-encl lofdf-juxt
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl
    lofdf-void lofdf-encl

    lofdf-void lfq
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl
    lofdf-void
    lofc3bx
    
    lfp lofdf-void lofdf-encl
    lofdf-void lfq
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl
    lofdf-void
    lofdf-void lofdf-encl
    lfp lofand.1 lofintr
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl
    lfp lfq lofdf-juxt lofdf-encl lofdf-juxt
    lfp lfq
    lfp lofdf-void lofdf-encl lfq
    lfp lofand.1 lofintr
    lfq lofand.2 lofintr
    lofeuc
    lofdf-NtoU
    lofintr
    lofrepbx
    
    lofeucr
    lofelim
    $.
  $}

  ${
    lofmp.1 $e |- `[ p `] q $.
    lofmp.2 $e |- p $.
    lofmp   $p |- q  $=
    lfq
    lfq lofdf-encl lofdf-encl  lfq  lofdf-void lofdf-encl

    lfq c1.0

    lofdf-void lofdf-encl lofdf-encl    lofdf-void
    lfq lofdf-encl   lofdf-void   lofdf-void   lofdf-void
    lofdf-void lofdf-encl

    lofdf-void c1.0 

    lfp lofdf-encl  lofdf-void lofdf-encl lofdf-encl
    lfq lofdf-encl lofdf-void lofdf-void lofdf-void lofdf-void lofdf-encl
    

    lfp lofdf-void lofdf-encl lfp lofmp.2 lofintr lofbeq

    
    lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl
    lfq lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl
    lofdf-void lofdf-encl

    lofdf-void    lfp lofdf-encl   lofdf-void  lfq   lofdf-void   lofdf-void
    lofdf-void    lofdf-void
    lofc2bx
    
    lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-juxt lofdf-encl
    lfp lofdf-encl lfq lofdf-juxt
    lfp
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

  $( The constants of classical propositional logic. $)
  $c ( ) -> -. $.
  $( PLEASE PUT DESCRIPTION HERE. $)
  wimp $a loff ( p -> q ) $.
  $( PLEASE PUT DESCRIPTION HERE. $)
  wneg $a loff -. p $.

  
  $( Define classical implication in terms of LoF. $)
  lofdf-imp $a |- ( p -> q ) `= `[ p `] q $.


  $( Define classical negation in terms of LoF. $)
  lofdf-neg $a |- -. p `= `[ p `] $.

  
  ax-1 $p |- ( p -> ( q -> p ) ) $=
    lfp lfq lfp wimp wimp
    
    lfp lfq lfp wimp wimp
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lfp lofdf-juxt
    lofdf-void lofdf-encl

    lfp lfq lfp wimp wimp
    lfp lofdf-encl lfq lfp wimp lofdf-juxt
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lfp lofdf-juxt
    lfp lfq lfp wimp
    lofdf-imp 
    
    lfq lfp wimp   lfq lofdf-encl lfp lofdf-juxt
    lfp lofdf-encl
    lfq lfp lofdf-imp
    lofsubr
    loftrans

    lfp lofdf-void lfq lofdf-encl lofdf-void
    lofc2e
    loftrans
    lofelim
    $.

  ax-2 $p |- ( ( p -> ( q -> r ) ) -> ( ( p -> q ) -> ( p -> r ) ) ) $=
    lfp lfq lfr wimp wimp lfp lfq wimp lfp lfr wimp wimp wimp

    lfp lfq lfr wimp wimp lfp lfq wimp lfp lfr wimp wimp wimp
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl
      lfp  lofdf-encl lofdf-juxt lfq lofdf-encl lofdf-juxt
      lfr lofdf-juxt
    lofdf-void lofdf-encl

    lfp lfq lfr wimp wimp lfp lfq wimp lfp lfr wimp wimp wimp
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl
      lfq  lofdf-encl lofdf-juxt lfp lofdf-encl lofdf-juxt
      lfr lofdf-juxt
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl
      lfp  lofdf-encl lofdf-juxt lfq lofdf-encl lofdf-juxt
      lfr lofdf-juxt


    lfp lfq lfr wimp wimp lfp lfq wimp lfp lfr wimp wimp wimp
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl
      lfp lofdf-encl lfq lofdf-juxt lofdf-encl lofdf-juxt lfp lofdf-encl lofdf-juxt
      lfr lofdf-juxt
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl
      lfq  lofdf-encl lofdf-juxt lfp lofdf-encl lofdf-juxt
      lfr lofdf-juxt

    lfq lfr wimp
    lfq lofdf-encl lfr lofdf-juxt
    lfp lofdf-encl
    lofdf-void lofdf-void
    lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-juxt lfr lofdf-juxt
    lfp lfq lfr wimp wimp lfp lfq wimp lfp lfr wimp wimp wimp

    lfq lfr lofdf-imp

    lfp lfq lfr wimp wimp
    lfp lofdf-encl lfq lfr wimp lofdf-juxt
    lofdf-void lofdf-void lofdf-void
    lfp lofdf-encl lfq lofdf-juxt lofdf-encl lfp lofdf-encl lofdf-juxt lfr lofdf-juxt
    lfp lfq lfr wimp wimp lfp lfq wimp lfp lfr wimp wimp wimp

    lfp lfq lfr wimp  lofdf-imp

    lfp lfq wimp
    lfp lofdf-encl lfq lofdf-juxt
    lofdf-void lofdf-void
    lfp lfq lfr wimp wimp lofdf-encl
    lfp lofdf-encl lfr lofdf-juxt
    lfp lfq lfr wimp wimp lfp lfq wimp lfp lfr wimp wimp wimp

    lfp lfq lofdf-imp
    

    lfp lfr wimp      lfp lofdf-encl lfr lofdf-juxt
    lfp lfq lfr wimp wimp lofdf-encl lfp lfq wimp lofdf-encl lofdf-juxt
    lofdf-void
    lfp lfq lfr wimp wimp lfp lfq wimp lfp lfr wimp wimp wimp

    lfp lfr lofdf-imp

    lfp lfq wimp   lfp lfr wimp  wimp
    lfp lfq wimp lofdf-encl lfp lfr wimp lofdf-juxt
    lfp lfq lfr wimp wimp lofdf-encl
    lofdf-void
    lfp lfq lfr wimp wimp lfp lfq wimp lfp lfr wimp wimp wimp
    
    lfp lfq wimp   lfp lfr wimp 
    lofdf-imp
       
    lfp lfq lfr wimp wimp
    lfp lfq wimp lfp lfr wimp wimp
    lofdf-imp
    
     lofreps
     lofreps
     lofrepbxs
     lofrepbxs
     lofrepbxs
    
    lofdf-void lfp lofdf-encl
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl
    lfq lofdf-void lfr
    lofc2x

    loftrans
    
    lfq lofdf-encl   lfp lofdf-encl
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lfr lofdf-juxt lofdf-encl
    lofdf-void
    lfr
    lofcmmx

    loftrans
    
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lfr lofdf-juxt
    lofdf-void lofdf-void lofdf-void
    lofc2e

    loftrans
    lofelim
    $.

  ax-3 $p |- ( ( -. p -> -. q ) -> ( q -> p ) )
       $=
    lfp wneg lfq wneg wimp lfq lfp wimp wimp

    lfp wneg lfq wneg wimp lfq lfp wimp wimp
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lfp lofdf-juxt
    lofdf-void lofdf-encl
    
    lfp wneg lfq wneg wimp lfq lfp wimp wimp
    lfp lofdf-encl lofdf-encl lofdf-encl lfq lofdf-encl lofdf-juxt lfp lofdf-juxt
    lfp lofdf-encl lfq lofdf-encl lofdf-juxt lfp lofdf-juxt

    lfp wneg lfq wneg wimp lfq lfp wimp wimp
    lfp lofdf-encl lofdf-encl lfq lofdf-encl lofdf-juxt lofdf-encl
      lfq lofdf-encl lofdf-juxt lfp lofdf-juxt
    lfp lofdf-encl lofdf-encl lofdf-encl lfq lofdf-encl lofdf-juxt lfp lofdf-juxt

    lfq wneg
    lfq lofdf-encl
    lfp lofdf-encl lofdf-encl
    lofdf-void
    lofdf-void
    lfq lofdf-encl lfp lofdf-juxt
    lfp wneg lfq wneg wimp lfq lfp wimp wimp

    lfq lofdf-neg

    lfp wneg lofdf-encl
    lfp lofdf-encl lofdf-encl
    lofdf-void
    lfq wneg
    lofdf-void
    lfq lofdf-encl lfp lofdf-juxt
    lfp wneg lfq wneg wimp lfq lfp wimp wimp

    lfp wneg lfp lofdf-encl   
    lfp lofdf-neg lofbeq 

    lfp wneg lfq wneg wimp
    lfp wneg lofdf-encl lfq wneg lofdf-juxt
    lofdf-void lofdf-void lofdf-void
    lfq lofdf-encl lfp lofdf-juxt
    lfp wneg lfq wneg wimp lfq lfp wimp wimp

    lfp wneg lfq wneg lofdf-imp 

    lfq lfp wimp
    lfq lofdf-encl lfp lofdf-juxt
    lfp wneg lfq wneg wimp lofdf-encl
    lofdf-void
    lfp wneg lfq wneg wimp lfq lfp wimp wimp

    lfq lfp lofdf-imp

    lfp wneg lfq wneg wimp lfq lfp wimp 
    lofdf-imp
    lofreps
 
    lofrepbxs
    lofrepbxs
    lofrepbxs
    
    lfp lofdf-encl lofdf-encl
    lfq lofdf-encl
    lofdf-void lofdf-void lofdf-void lfp
    lofc2x

    loftrans
    
    lfp lofdf-void lofdf-void lofdf-void lfq lofdf-encl lfp lofdf-juxt
    lofc1bx

    loftrans
    
    lfp lofdf-void lfq lofdf-encl lofdf-void   
    lofc2e

    loftrans
    lofelim
    $.

  ${
    $( Minor premise for modus ponens. $)
    min $e |- p $.
    $( Major premise for modus ponens. $)
    maj $e |- ( p -> q ) $.
    ax-mp $p |- q $=
    lfp lfq
    lfp lofdf-encl lfq lofdf-juxt
    lfp lfq wimp
    lfp lofdf-encl lfq lofdf-juxt
    lofdf-void lofdf-encl

    lfp lfq lofdf-imp 
    lfp lfq wimp  maj lofintr
    lofeucr
    lofelim
    min
    lofmp
    $.
  $}
 

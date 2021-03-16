$( lofsetpq.mm - Version of 30-Sep-2017 $)

$(
  Version 0.3.0
  Copyright (C) 2015-2017 Naip Moro

  This file is made available under the MIT License:
  http://opensource.org/licenses/MIT
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                              0. Introduction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  In lof.mm ( https://github.com/naipmoro/lofmm/blob/master/lof.mm ) I
  presented metamath derivations of Spencer-Brown's Primary Algebra (details of
  the algebra, hereafter cited as "LoF", can be found in Chapter 6 of
  [Spencer-Brown]).  lof.mm was a stand-alone project indifferent to
  compatibility with set.mm, metamath's ongoing formalization of mathematics.
  In contrast, here I present a version which is strictly compatible:  I derive
  set.mm's propositional calculus from LoF.  There is nothing surprising in
  this -- classical propositional logic is one of the interpretations of LoF
  (Boolean algebra is another).  The real interest lies in the means of
  derivation.

  LoF is an equational logic (although I show that, technically, equations can
  be avoided).  In other words, axioms and theorems are stated in the form
  "p = q" .  Transitioning from this to the implicational form characteristic
  of classical propositional logic is an interesting problem.  I believe the
  technique chosen here is among the simplest, relying on a single additional
  axiom 'ax-qny' (known as Equanimity), the equational analogue of modus
  ponens:

  ${
    ax-qny.1 $e |- p $.
    ax-qny.2 $e |- p = q $.
    ax-qny   $a |- q $.
  $}

  With this rule in hand, and with appropriate definitions of "implies" and
  "not", I prove the axioms of set.mm, ax-1, ax-2, ax-3, and ax-mp, as theorems
  of LoF.
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                    1. The alphabet of boundary algebra
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare the primitive constant symbols. $)
  $c [ $. $( Left side of boundary $)
  $c ] $. $( Right side of boundary $)
  $c wff $. $( Well-formed formula symbol (read:  "the following symbol
               sequence is a wff of boundary algebra") $)
  $c |- $. $( Turnstile (read:  "the following symbol sequence is provable" or
              "a proof exists for") $)

  $( Introduce variables to represent the well-formed formulas. $)
  $v p q r s t u v w x y z k $.

  $( Specify some variables that we will use to represent wffs. $)
  $( Let variable p be a wff. $)
  llp $f wff p $.
  $( Let variable q be a wff. $)
  llq $f wff q $.
  $( Let variable r be a wff. $)
  llr $f wff r $.
  $( Let variable s be a wff. $)
  lls $f wff s $.
  $( Let variable t be a wff. $)
  llt $f wff t $.
  $( Let variable u be a wff. $)
  llu $f wff u $.
  $( Let variable v be a wff. $)
  llv $f wff v $.
  $( Let variable w be a wff. $)
  llw $f wff w $.
  $( Let variable x be a wff. $)
  llx $f wff x $.
  $( Let variable y be a wff. $)
  lly $f wff y $.
  $( Let variable z be a wff. $)
  llz $f wff z $.
  $( Let variable k be a wff. $)
  llk $f wff k $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   2. Recursive definition of LoF wffs
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  It is worth noting that the following recursive definition of wffs precisely
  mirrors the definition of the Dyck language (aka "parenthesis language") via
  a context-free grammar: S -> e | [S] | SS (where e is the empty string).
  Every boundary expression without variables corresponds to a word of the Dyck
  language and vice versa.
$)

  $( Empty space, the void, is the lone atomic wff.  Spencer-Brown refers to it
     as the "unmarked state" and in our intended interpretation it will be
     identified with the truth value False.  Had we interpreted it as True, we
     would be working in (a version of) Charles S. Peirce's alpha system.
     (Contributed by Naip Moro, 2-Sep-2015.) $)
  df-void $a wff $.

  $( If p is a wff, so is [ p ] .  We say that "p is enclosed (or crossed, or
     marked)".  Combined with the previous definition, we see that [ ] ,
     [ [ ] ] , [ ... [ [ ] ] ... ] are all wffs.  Spencer-Brown calls [ ] the
     "marked state" and we identify it with the value True.  (Contributed by
     Naip Moro, 2-Sep-2015.) $)
  df-encl $a wff [ p ] $.

  $( If p and q are wffs, so is p q .  Note:  This rule introduces a
     technical ambiguity into the metamath formal language and some parsers
     will reject it.  However, since the system is inherently associative, this
     ambiguity does not compromise the validity of the formal derivations and
     all proper validators will accept them.  (Contributed by Naip Moro,
     2-Sep-2015.) $)
  df-juxt $a wff p q $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                  3. The four primitive inference axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  In lof.mm "=" was one of the primitive constants of the language.  But the
  symbol is superfluous, as in a Boolean system equality and equivalence are
  synonyms.  Let us interpret the form [ [ p ] [ q ] ] [ p q ] to mean
  " p equals (or is equivalent to) q".  All of LoF can be expressed accordingly
  and I will call this the "unitary form" of LoF.  For demonstration purposes,
  I state the four primitive inference rules of LoF and a handful of associated
  theorems in this form.  But what is theoretically possible is not always
  cognitively palatable, and I subsequently abandon this approach and return to
  explicit equations, what I call LoF's "equational form".
$)

  ${
    ax-euc.1 $e |- [ [ p ] [ q ] ] [ p q ] $.
    ax-euc.2 $e |- [ [ r ] [ q ] ] [ r q ] $.
    $( Read this as:  "If p is equal to q and r is equal to q , then we can
       infer that p is equal to r ".  In other words, two things equal to the
       same thing are equal to each other.  This is Euclid's first Common
       Notion and, in an equational logic, this and its sibling, transitivity,
       are the main engine of derivation.  (Contributed by Naip Moro,
       26-Jan-2017.) $)
    ax-euc $a |- [ [ p ] [ r ] ] [ p r ] $.
  $}

  $( We can rephrase Euclid's second and third Common Notions as:  doing the
     same thing (e.g., applying the same operation) to equal things leaves
     equal things.  In light of our two operations, enclosure and
     juxtaposition, this leads to the next two axioms (looked at differently,
     these can also be seen as substitution/replacement rules). $)

  ${
    ax-beq.1 $e |- [ [ p ] [ q ] ] [ p q ] $.
    $( Read this as:  "If p is equal to q , then we can infer that
       [ p ] is equal to [ q ]".  Enclosing equal forms leaves equal
       forms.  (Contributed by Naip Moro, 26-Jan-2017.) $)
    ax-beq $a |- [ [ [ p ] ] [ [ q ] ] ] [ [ p ] [ q ] ] $.
  $}

  ${
    ax-sub.1 $e |- [ [ p ] [ q ] ] [ p q ] $.
    $( Read this as:  "If p is equal to q , then we can infer that p v is equal
       to q v for any v".  Juxtaposing the same form with equal forms leaves
       equal forms.  (Contributed by Naip Moro, 26-Jan-2017.) $)
    ax-sub $a |- [ [ p v ] [ q v ] ] [ p v q v ] $.
  $}

  $( Read this as:  "p q is equal to q p".  Of the four, this commutativity
     axiom is the only one that is domain-specific. (Contributed by Naip Moro,
     26-Jan-2017.) $)
  ax-cmm $a |- [ [ p q ] [ q p ] ] [ p q q p ] $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                           4. Inference theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  If our target interpretation is to be satisfied, we should expect "equality"
  to meet the requirements of an equivalence relation: reflexivity, symmetry,
  and transitivity.  The next three theorems show that it does.
$)

  $( "Equality" is reflexive.  Read this as:  "p is equal to p". (Contributed
     by Naip Moro, 26-Jan-2017.) $)
 idu $p |- [ [ p ] [ p ] ] [ p p ] $=
   llp df-void ax-cmm $.

  ${
    symu.1 $e |- [ [ p ] [ q ] ] [ p q ] $.
    $( "Equality" is symmetric.  Read this as:  "If p is equal to q , then we
       can infer that q is equal to p".  (Contributed by Naip Moro,
       26-Jan-2017.) $)
    symu $p |- [ [ q ] [ p ] ] [ q p ] $=
      llq llq llp llq idu symu.1 ax-euc $.
  $}

  ${
    tranu.1 $e |- [ [ p ] [ q ] ] [ p q ] $.
    tranu.2 $e |- [ [ q ] [ r ] ] [ q r ] $.
    $( "Equality" is transitive.  Read this as:  "If p is equal to q and q is
       equal to r, then we can infer that p is equal to r".  (Contributed by
       Naip Moro, 26-Jan-2017.) $)
    tranu $p |- [ [ p ] [ r ] ] [ p r ] $=
      llp llq llr tranu.1 llq llr tranu.2 symu ax-euc $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                     5. Introducing the equality symbol
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  We can go only so far with the unitary form before reasoning becomes
  intolerably cumbersome.  In introducing "=", note that it is a relation
  between wffs and not itself part of a wff.
$)

  $c = $. $( Equality.  Read:  "is equal to" or "is equivalent to") $)

  ${
    df-equ.1 $e |- p = q $.
    $( Define equality in terms of LoF's unitary formalism.  (Contributed by
       Naip Moro, 26-Jan-2017.) $)
    df-equ $a |- [ [ p ] [ q ] ] [ p q ] $.
  $}

  ${
    df-uni.1 $e |- [ [ p ] [ q ] ] [ p q ] $.
    $( Translate LoF's unitary form into equational form.  (Contributed by Naip
       Moro, 26-Jan-2017.) $)
    df-uni $a |- p = q $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                     6. Equality-based inference theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Traditional equational logic is based on four inference rules
  (see https://en.wikipedia.org/wiki/Equational_logic ):

  <HTML><br></HTML>

  <HTML><ul>
  <li><b>Substitution.</b>
  If P is a theorem, replacing all occurrences of some variable x with any wff
  Q is also a theorem.
  </li>
  <li><b>Leibniz.</b>
  If P = Q then replacing all occurrences of some variable x in any wff F with
  P is equivalent to replacing all occurrences of x with Q.
  </li>
  <li><b>Transitivity.</b>
  From P = Q and Q = R we can infer P = R.
  </li>
  <li><b>Equanimity.</b>
  From P and P = Q we can infer Q.
  </li>
  </ul></HTML>

  At this point in the derivation, nothing approaching the power first-order
  logic is available, so the generality of the Leibniz rule is unattainable
  Since we are developing this system ex nihilo, FOL is unavailable and we
  have no means to match the generality of the Leibniz rule...
  How does this compare with LoF? For one thing, Substitution is not needed,
  as it is pre-built into metamath.  The generality of the Leibniz rule is
  conceptually captured by our two simple rules 'beq' and 'sub', while
  Transitivity is replaced by Euclid's equivalent rule 'euc' (we prove
  Transitivity as a theorem).  Finally, Equanimity is not needed until we begin
  to interface with classical propositional logic (and even then there might be
  a simpler approach).  This suggests that LoF is more accurately characterized
  as a proto-equational logic.  It's true that LoF's formal system requires
  commutativity, clearly an extraneous addition; but bear in mind that LoF is
  intrinsically a planar notation, where commutativity is an unstated given. It
  is only in the context of a linear notation like metamath that an explicit
  reference to commutativity is required.
$)

  ${
    euc.1 $e |- p = q $.
    euc.2 $e |- r = q $.
    $( The equational-form version of 'ax-euc'.  (Contributed by Naip Moro,
       26-Jan-2017.) $)
    euc $p |- p = r $=
      llp llr llp llq llr llp llq euc.1 df-equ llr llq euc.2 df-equ ax-euc
      df-uni $.
  $}

  ${
    beq.1 $e  |- p = q $.
    $( The equational-form version of 'ax-beq'.  (Contributed by Naip Moro,
       26-Jan-2017.) $)
    beq $p |- [ p ] = [ q ] $=
      llp df-encl llq df-encl llp llq llp llq beq.1 df-equ ax-beq df-uni $.
  $}

  ${
    sub.1 $e |- p = q $.
    $( The equational-form version of 'ax-sub'.  (Contributed by Naip Moro,
       26-Jan-2017.) $)
    sub $p |- p v = q v $=
      llp llv df-juxt llq llv df-juxt llp llq llv llp llq sub.1 df-equ ax-sub
      df-uni $.
  $}

  $( The equational-form version of 'ax-cmm'.  (Contributed by Naip Moro,
     26-Jan-2017.) $)
  cmm $p |- p q = q p $=
    llp llq df-juxt llq llp df-juxt llp llq ax-cmm df-uni $.

  $( The equational-form version of 'idu'.  (Contributed by Naip Moro,
     6-Sep-2015.) $)
  id $p |- p = p $=
    llp df-void cmm $.

  ${
    sym.1 $e |- p = q $.
    $( The equational-form version of 'symu'.  (Contributed by Naip Moro,
       2-Sep-2015.) $)
    sym $p |- q = p $=
      llq llq llp llq id sym.1 euc $.
  $}

  ${
    tran.1 $e |- p = q $.
    tran.2 $e |- q = r $.
    $( The equational-form version of 'tranu'.  (Contributed by Naip Moro,
       2-Sep-2015.) $)
    tran $p |- p = r $=
      llp llq llr tran.1 llq llr tran.2 sym euc $.
  $}

  ${
    eucr.1 $e |- p = q $.
    eucr.2 $e |- p = r $.
    $( A commuted - or reversed - version of 'euc'.  (Contributed by Naip
       Moro, 2-Sep-2015.) $)
    eucr $p |- q = r $=
      llq llp llr llp llq eucr.1 sym eucr.2 tran $.
  $}

  ${
    subr.1 $e |- p = q $.
    $( A commuted version of 'sub'.  (Contributed by Naip Moro, 2-Sep-2015.) $)
    subr $p |- u p = u q $=
      llq llu df-juxt llu llp df-juxt llu llq df-juxt llp llu df-juxt llq llu
      df-juxt llu llp df-juxt llp llq llu subr.1 sub llp llu cmm eucr llq llu
      cmm eucr $.
  $}

  $( More versions of replacement/substitution. $)
  ${
    subst.1 $e |- p = q $.
    $( Replace a form with an equal form within an extended form.  (Contributed
       by Naip Moro, 2-Sep-2015.) $)
    subst $p |- u p v = u q v $=
      llp llv df-juxt llq llv df-juxt llu llp llq llv subst.1 sub subr $.
  $}

  ${
    substr.1 $e |- p = q $.
    $( Replace a form with an equal form within a commuted extended form.
       (Contributed by Naip Moro, 2-Sep-2015.) $)
    substr $p |- u p v = v q u $=
      llu llp df-juxt llv df-juxt llu llv df-juxt llq df-juxt llv llq df-juxt
      llu df-juxt llp llv df-juxt llv llq df-juxt llu llp llv df-juxt llq llv
      df-juxt llv llq df-juxt llp llq llv substr.1 sub llq llv cmm tran subr
      llu llv llq df-juxt cmm tran $.
  $}

  ${
    subb1.1 $e |- p = q $.
    $( Replace a form with an equal form within a bounded extended form.
       (Contributed by Naip Moro, 2-Sep-2015.) $)
    subb1 $p |- w [ u p v ] x = w [ u q v ] x $=
      llu llp df-juxt llv df-juxt df-encl llu llq df-juxt llv df-juxt df-encl
      llw llx llu llp df-juxt llv df-juxt llu llq df-juxt llv df-juxt llp llq
      llu llv subb1.1 subst beq subst $.
  $}

  ${
    subbd1.1 $e |- p = q $.
    $( Replace a form with an equal form within a double-bounded extended
       form.  (Contributed by Naip Moro, 25-Feb-2017.) $)
    subbd1 $p |- y [ w [ u p v ] x ] z = y [ w [ u q v ] x ] z $=
      llw llu llp df-juxt llv df-juxt df-encl df-juxt llx df-juxt llw llu llq
      df-juxt llv df-juxt df-encl df-juxt llx df-juxt df-void df-void lly llz
      llp llq llu llv llw llx subbd1.1 subb1 subb1 $.
  $}

  ${
    subb2.1 $e |- p = q $.
    $( Replace a form with an equal form within a bounded and commuted extended
       form.  (Contributed by Naip Moro, 2-Sep-2015.) $)
    subb2 $p |- w [ u p v ] x = w [ v q u ] x $=
      llu llp df-juxt llv df-juxt df-encl llv llq df-juxt llu df-juxt df-encl
      llw llx llu llp df-juxt llv df-juxt llv llq df-juxt llu df-juxt llp llq
      llu llv subb2.1 substr beq subst $.
  $}

  ${
    rep.1 $e |- p = q $.
    rep.2 $e |- u p v = y $.
    $( Direct substitution into lhs of an equation.  (Contributed by Naip Moro,
       18-Sep-2015.) $)
    rep $p |- u q v = y $=
      llu llp df-juxt llv df-juxt llu llq df-juxt llv df-juxt lly llp llq llu
      llv rep.1 subst rep.2 eucr $.
  $}

  ${
    reps.1 $e |- p = q $.
    reps.2 $e |- y = u p v $.
    $( Direct substitution into rhs of an equation.  (Contributed by Naip Moro,
       14-Feb-2017.) $)
    reps $p |- y = u q v $=
      llu llq df-juxt llv df-juxt lly llp llq llu llv lly reps.1 lly llu llp
      df-juxt llv df-juxt reps.2 sym rep sym $.
  $}

  ${
    repbx.1 $e |- p = q $.
    repbx.2 $e |- w [ u p v ] x = y $.
    $( Direct substitution into lhs of a bounded-form equation.  (Contributed
       by Naip Moro, 18-Sep-2015.) $)
    repbx $p |- w [ u q v ] x = y $=
      llw llu llp df-juxt llv df-juxt df-encl df-juxt llx df-juxt llw llu llq
      df-juxt llv df-juxt df-encl df-juxt llx df-juxt lly llp llq llu llv llw
      llx repbx.1 subb1 repbx.2 eucr $.
  $}

  ${
    repbdx.1 $e |- p = q $.
    repbdx.2 $e |- y [ w [ u p v ] x ] z = k $.
    $( Direct substitution into lhs of a double-bounded equation.  (Contributed
       by Naip Moro, 27-Feb-2017.) $)
    repbdx $p |- y [ w [ u q v ] x ] z = k $=
      lly llw llu llp df-juxt llv df-juxt df-encl df-juxt llx df-juxt df-encl
      df-juxt llz df-juxt lly llw llu llq df-juxt llv df-juxt df-encl df-juxt
      llx df-juxt df-encl df-juxt llz df-juxt llk llp llq llu llv llw llx lly
      llz repbdx.1 subbd1 repbdx.2 eucr $.
  $}

  ${
    repbxs.1 $e |- p = q $.
    repbxs.2 $e |- y = w [ u p v ] x $.
    $( Direct substitution into rhs of a bounded equation.  (Contributed by
       Naip Moro, 14-Feb-2017.) $)
    repbxs $p |- y = w [ u q v ] x $=
      llw llu llq df-juxt llv df-juxt df-encl df-juxt llx df-juxt lly llp llq
      llu llv llw llx lly repbxs.1 lly llw llu llp df-juxt llv df-juxt df-encl
      df-juxt llx df-juxt repbxs.2 sym repbx sym $.
  $}

  ${
    repbdxs.1 $e |- p = q $.
    repbdxs.2 $e |- k = y [ w [ u p v ] x ] z $.
    $( Direct substitution into rhs of a double-bounded equation.  (Contributed
       by Naip Moro, 27-Feb-2017.) $)
    repbdxs $p |- k = y [ w [ u q v ] x ] z $=
      lly llw llu llq df-juxt llv df-juxt df-encl df-juxt llx df-juxt df-encl
      df-juxt llz df-juxt llk llp llq llu llv llw llx lly llz llk repbdxs.1 llk
      lly llw llu llp df-juxt llv df-juxt df-encl df-juxt llx df-juxt df-encl
      df-juxt llz df-juxt repbdxs.2 sym repbdx sym $.
  $}

  ${
    repbd.1 $e |- p = q $.
    repbd.2 $e |- [ [ u p v ] ] = y $.
    $( Direct substitution into lhs of a double-bounded equation.  (Contributed
       by Naip Moro, 3-Oct-2015.) $)
    repbd $p |- [ [ u q v ] ] = y $=
      llu llp df-juxt llv df-juxt df-encl df-encl llu llq df-juxt llv df-juxt
      df-encl df-encl lly llu llp df-juxt llv df-juxt df-encl llu llq df-juxt
      llv df-juxt df-encl llp llq llu llv df-void df-void repbd.1 subb1 beq
      repbd.2 eucr $.
  $}

  ${
    quad.1 $e |- p = q $.
    quad.2 $e |- r = s $.
    $( Double substitution of equivalent forms.  (Contributed by Naip Moro,
       2-Sep-2015.) $)
    quad $p |- p r = q s $=
      llp llr df-juxt llq llr df-juxt llq lls df-juxt llp llq df-void llr
      quad.1 subst llr lls llq df-void quad.2 subst tran $.
  $}

  ${
    ins.1 $e |- p q = r s $.
    $( Insert the same form into two equivalent forms.  (Contributed by Naip
       Moro, 3-Sep-2015.) $)
    ins $p |- p v q = r v s $=
      llp llv df-juxt llq df-juxt llv llr df-juxt lls df-juxt llr llv df-juxt
      lls df-juxt llp llv df-juxt llq df-juxt llv llp df-juxt llq df-juxt llv
      llr df-juxt lls df-juxt llp llv df-juxt llv llp df-juxt llq llp llv cmm
      sub llp llq df-juxt llr lls df-juxt llv ins.1 subr tran llv llr df-juxt
      llr llv df-juxt lls llv llr cmm sub tran $.
  $}

  $( Extended commutativity.  (Contributed by Naip Moro, 3-Sep-2015.) $)
  cmmx $p  |- u p v q w = u q v p w $=
    llp llv df-juxt llq df-juxt llq llv df-juxt llp df-juxt llu llw llp llq llq
    llp llv llp llq cmm ins subst $.

  $( Bounded and extended commutativity.  (Contributed by Naip Moro,
     2-Sep-2015.) $)
  cmmbx $p |- x [ u p v q w ] y = x [ u q v p w ] y $=
    llp llv df-juxt llq df-juxt llq llv df-juxt llp df-juxt llu llw llx lly llv
    llv llp llq llv id substr subb1 $.

  $( Double-bounded and extended commutativity.  (Contributed by Naip Moro,
     25-Feb-2017.) $)
  cmmbdx $p |- z [ x [ u p v q w ] y ] k = z [ x [ u q v p w ] y ] k $=
    llx llu llp df-juxt llv df-juxt llq df-juxt llw df-juxt df-encl df-juxt lly
    df-juxt llx llu llq df-juxt llv df-juxt llp df-juxt llw df-juxt df-encl
    df-juxt lly df-juxt df-void df-void llz llk llp llq llu llv llw llx lly
    cmmbx subb1 $.

  ${
    quadbx.1 $e |- p = q $.
    quadbx.2 $e |- r = s $.
    $( Double substitution into a bounded and extended form.  (Contributed by
       Naip Moro, 3-Sep-2015.) $)
    quadbx $p |- x [ u p v r w ] y = x [ u q v s w ] y $=
      llp llv df-juxt llr df-juxt llq llv df-juxt lls df-juxt llu llw llx lly
      llp llr llq lls llv llp llq llr lls quadbx.1 quadbx.2 quad ins subb1 $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                                 7. Axioms of LoF
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  See lof.mm for a discussion of different sets of axioms for LoF.  Here I
  adopt the original set of [Spencer-Brown] p. 28.  The descriptive names of
  axioms and theorems are Spencer-Brown's own.
$)

  $( Position.  Axiom J1 of [Spencer-Brown] p. 28.  (Contributed by Naip Moro,
     6-Sep-2015.) $)
  ax-j1 $a |- [ [ p ] p ] = $.

  $( Transposition.  Axiom J2 of [Spencer-Brown] p. 28.  (Contributed by Naip
     Moro, 6-Sep-2015.) $)
  ax-j2 $a |- [ [ p r ] [ q r ] ] = [ [ p ] [ q ] ] r $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                                8. Theorems of LoF
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The theorems, which Spencer-Brown calls Consequences, are from Chapter 6 of
  [Spencer-Brown].
$)

  $( Reflexion.  Theorem C1 of [Spencer-Brown] p. 28.  (Contributed by Naip
     Moro, 20-Feb-2017.) $)
  c1 $p |- [ [ p ] ] = p $=
    llp df-encl df-encl llp df-encl df-encl llp df-juxt df-encl llp df-encl llp
    df-juxt df-encl df-juxt df-encl llp llp df-encl df-encl llp llp df-encl
    df-encl df-juxt df-encl df-encl llp df-encl df-encl llp df-juxt df-encl llp
    df-encl llp df-juxt df-encl df-juxt df-encl llp df-encl df-encl llp df-encl
    df-juxt df-encl df-void df-void llp llp df-encl df-encl df-juxt df-encl
    df-void df-void llp df-encl df-encl llp df-encl ax-j1 llp df-encl llp
    df-encl df-encl df-juxt df-encl llp df-encl df-encl llp df-encl df-juxt
    df-encl df-void llp llp df-encl df-encl df-juxt df-encl df-void df-void llp
    df-encl df-encl llp df-encl llp df-encl df-encl df-void df-void df-void
    df-void df-void cmmbx llp df-encl df-encl llp df-encl df-encl llp df-encl
    df-juxt df-encl llp df-encl df-encl df-juxt llp df-encl llp df-encl df-encl
    df-juxt df-encl llp llp df-encl df-encl df-juxt df-encl df-juxt df-encl llp
    df-encl df-encl llp df-encl df-juxt df-encl llp df-encl df-encl df-juxt llp
    df-encl df-encl llp df-encl df-encl llp df-encl df-juxt df-encl df-void llp
    df-encl df-encl llp df-encl ax-j1 sub sym llp df-encl llp llp df-encl
    df-encl ax-j2 euc repbxs repbxs llp llp df-encl df-encl df-juxt df-encl llp
    df-encl df-encl llp df-juxt df-encl df-void llp df-encl llp df-juxt df-encl
    df-void df-void df-void df-void df-void llp llp df-encl df-encl df-void
    df-void df-void df-void df-void cmmbx llp df-encl llp df-juxt df-encl
    df-void llp ax-j1 sym quadbx tran llp df-encl df-encl llp df-juxt df-encl
    llp df-encl llp df-juxt df-encl df-juxt df-encl llp df-encl df-encl df-encl
    llp df-encl df-encl df-juxt df-encl llp df-juxt llp llp df-encl df-encl llp
    df-encl llp ax-j2 llp df-encl df-encl df-encl llp df-encl df-encl df-juxt
    df-encl df-void llp llp df-encl df-encl ax-j1 sub tran tran $.

  $( Generation.  Theorem C2 of [Spencer-Brown] p. 32.  (Contributed by Naip
     Moro, 6-Sep-2015.) $)
  c2 $p |- [ p q ] q = [ p ] q $=
    llp df-encl llq df-juxt df-encl llq df-encl llq df-juxt df-encl df-juxt
    df-encl llp llq df-juxt df-encl llq df-juxt llp df-encl llq df-juxt llp
    df-encl llq df-juxt df-encl llq df-encl llq df-juxt df-encl df-juxt df-encl
    llp df-encl df-encl llq df-encl df-encl df-juxt df-encl llq df-juxt llp llq
    df-juxt df-encl llq df-juxt llp df-encl llq df-encl llq ax-j2 llp df-encl
    df-encl llp llq df-encl df-encl llq df-void df-void df-void df-void llq llp
    c1 llq c1 quadbx tran llp df-encl llq df-juxt df-encl llq df-encl llq
    df-juxt df-encl df-juxt df-encl llp df-encl llq df-juxt df-encl df-encl llp
    df-encl llq df-juxt llq df-encl llq df-juxt df-encl df-void llp df-encl llq
    df-juxt df-encl df-void df-void df-void llq ax-j1 subb1 llp df-encl llq
    df-juxt c1 tran eucr $.

  $( Integration.  Theorem C3 of [Spencer-Brown] p. 32.  (Contributed by
     Naip Moro, 6-Sep-2015.) $)
  c3 $p |- [ ] p = [ ] $=
    llp df-encl llp df-juxt df-void df-encl llp df-juxt df-void df-encl df-void
    llp c2 llp df-encl llp df-juxt df-encl df-encl llp df-encl llp df-juxt
    df-void df-encl llp df-encl llp df-juxt c1 llp df-encl llp df-juxt df-encl
    df-void llp ax-j1 beq eucr eucr $.

  $( Occultation.  Theorem C4 of [Spencer-Brown] p. 33.  (Contributed by Naip
     Moro, 6-Sep-2015.)  (Proof shortened by Naip Moro, 13-Oct-2017.) $)
  c4 $p |- [ [ p ] q ] p = p $=
    llp llp df-encl llq df-juxt df-encl llp df-juxt llp llq df-juxt df-encl llp
    llq df-juxt df-juxt df-encl df-void df-void llp llp df-encl llq df-juxt
    df-encl llp df-juxt llp llq df-juxt ax-j1 llq llp df-juxt llp llq df-juxt
    llp llq df-juxt df-encl df-void df-void llp llp df-encl llq df-juxt df-encl
    llp df-juxt llq llp cmm llp df-encl llq df-juxt llp llq df-juxt df-encl llq
    df-juxt df-void llp df-void llp llp df-encl llq df-juxt df-encl llp df-juxt
    llp llq df-juxt df-encl llq df-juxt llp df-encl llq df-juxt llp llq c2 sym
    llp df-encl llq df-juxt llp c2 repbx repbx rep sym $.

  $( Corollary of C4.  (Contributed by Naip Moro, 18-Sep-2015.) $)
  c4cor $p |- [ p q ] [ p ] = [ p ] $=
    llp df-encl df-encl llq df-juxt df-encl llp df-encl df-juxt llp llq df-juxt
    df-encl llp df-encl df-juxt llp df-encl llp df-encl df-encl llp df-void llq
    df-void llp df-encl llp c1 subb1 llp df-encl llq c4 eucr $.

  $( Iteration.  Theorem C5 of [Spencer-Brown] p. 33.  (Contributed by Naip
     Moro, 6-Sep-2015.) $)
  c5 $p |- p p = p $=
    llp df-encl llp df-juxt df-encl llp df-juxt llp llp df-juxt llp llp df-encl
    llp df-juxt df-encl llp df-juxt llp df-encl df-encl llp df-juxt llp llp
    df-juxt llp df-encl llp c2 llp df-encl df-encl llp df-void llp llp c1 subst
    tran llp df-encl llp df-juxt df-encl df-void df-void llp llp ax-j1 subst
    eucr $.

  $( Extension.  Theorem C6 of [Spencer-Brown] p. 33.  (Contributed by Naip
     Moro, 6-Sep-2015.) $)
  c6 $p |- [ [ p ] [ q ] ] [ [ p ] q ] = p $=
    llp df-encl llq df-encl df-juxt df-encl llp df-encl llq df-juxt df-encl
    df-juxt llp df-encl df-encl llp llp df-encl llq df-encl df-juxt df-encl llp
    df-encl llq df-juxt df-encl df-juxt df-encl df-encl llp df-encl llq df-encl
    df-juxt df-encl llp df-encl llq df-juxt df-encl df-juxt llp df-encl df-encl
    llp df-encl llq df-encl df-juxt df-encl llp df-encl llq df-juxt df-encl
    df-juxt c1 llp df-encl llq df-encl df-juxt df-encl llp df-encl llq df-juxt
    df-encl df-juxt df-encl df-encl llq df-encl df-encl llq df-encl df-juxt
    df-encl llp df-encl df-juxt df-encl llp df-encl df-encl llp df-encl llq
    df-encl df-juxt df-encl llp df-encl llq df-juxt df-encl df-juxt df-encl llq
    df-encl df-encl llq df-encl df-juxt df-encl llp df-encl df-juxt llp df-encl
    llq df-encl df-juxt df-encl llp df-encl llq df-juxt df-encl df-juxt df-encl
    llq df-encl llp df-encl df-juxt df-encl llq llp df-encl df-juxt df-encl
    df-juxt df-encl llq df-encl df-encl llq df-encl df-juxt df-encl llp df-encl
    df-juxt llp df-encl llq df-encl df-juxt df-encl llq df-encl llp df-encl
    df-juxt df-encl llp df-encl llq df-juxt df-encl llq llp df-encl df-juxt
    df-encl df-void df-void df-void df-void df-void llp df-encl llq df-encl
    df-void df-void df-void df-void df-void cmmbx llp df-encl llq df-void
    df-void df-void df-void df-void cmmbx quadbx llq df-encl llq llp df-encl
    ax-j2 tran beq llq df-encl df-encl llq df-encl df-juxt df-encl df-void
    df-void llp df-encl df-void df-void llq df-encl ax-j1 subb1 tran eucr llp
    c1 tran $.

  $( Corollary of C6.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  c6cor $p |- [ [ p ] q ] [ p q ] = [ q ] $=
    llq llp df-juxt llp llq df-juxt df-void df-void llp df-encl llq df-juxt
    df-encl df-void llq df-encl llq llp cmm llq llp df-encl df-juxt llp df-encl
    llq df-juxt df-void df-void df-void llq llp df-juxt df-encl llq df-encl llq
    llp df-encl cmm llq df-encl df-encl llq df-void llp llq llp df-encl df-juxt
    df-encl df-void llq df-encl llq c1 llq df-encl df-encl llq df-void llp
    df-encl df-void llq df-encl df-encl llp df-juxt df-encl llq df-encl llq c1
    llq df-encl llp c6 repbx repbx repbx repbx $.

  $( Echelon.  Theorem C7 of [Spencer-Brown] p. 34.  (Contributed by Naip Moro,
     6-Sep-2015.) $)
  c7 $p |- [ [ [ p ] q ] r ] = [ p r ] [ [ q ] r ] $=
    llp llr df-juxt df-encl llq df-encl llr df-juxt df-encl df-juxt df-encl
    df-encl llp df-encl llq df-juxt df-encl llr df-juxt df-encl llp llr df-juxt
    df-encl llq df-encl llr df-juxt df-encl df-juxt llp llr df-juxt df-encl llq
    df-encl llr df-juxt df-encl df-juxt df-encl df-encl llp df-encl llq df-encl
    df-encl df-juxt df-encl llr df-juxt df-encl llp df-encl llq df-juxt df-encl
    llr df-juxt df-encl llp llr df-juxt df-encl llq df-encl llr df-juxt df-encl
    df-juxt df-encl llp df-encl llq df-encl df-encl df-juxt df-encl llr df-juxt
    llp llq df-encl llr ax-j2 beq llp df-encl llq df-encl df-encl df-juxt
    df-encl llr df-juxt llp df-encl llq df-juxt df-encl llr df-juxt llq df-encl
    df-encl llq llp df-encl df-void df-void llr llq c1 subb1 beq tran llp llr
    df-juxt df-encl llq df-encl llr df-juxt df-encl df-juxt c1 eucr $.

  $( Modified transposition.  Theorem C8 of [Spencer-Brown] p. 34.
     (Contributed by Naip Moro, 6-Sep-2015.) $)
  c8 $p |- [ [ p ] [ q s ] [ r s ] ] = [ [ p ] [ q ] [ r ] ] [ [ p ] [ s ] ] $=
    llp df-encl llq lls df-juxt df-encl df-juxt llr lls df-juxt df-encl df-juxt
    df-encl llq df-encl llr df-encl df-juxt df-encl lls df-juxt df-encl llp
    df-encl df-juxt df-encl llp df-encl llq df-encl df-juxt llr df-encl df-juxt
    df-encl llp df-encl lls df-encl df-juxt df-encl df-juxt llq lls df-juxt
    df-encl llr lls df-juxt df-encl df-juxt df-encl df-encl llq lls df-juxt
    df-encl llr lls df-juxt df-encl df-juxt llp df-encl df-void df-void df-void
    llq df-encl llr df-encl df-juxt df-encl lls df-juxt df-encl llp df-encl
    df-juxt df-encl llq lls df-juxt df-encl llr lls df-juxt df-encl df-juxt c1
    llq lls df-juxt df-encl llr lls df-juxt df-encl df-juxt df-encl df-encl llq
    df-encl llr df-encl df-juxt df-encl lls df-juxt df-encl llp df-encl df-void
    df-void df-void llq lls df-juxt df-encl llr lls df-juxt df-encl df-juxt
    df-encl llq df-encl llr df-encl df-juxt df-encl lls df-juxt llq llr lls
    ax-j2 beq subb2 repbx llq df-encl llr df-encl df-juxt df-encl lls df-juxt
    df-encl llp df-encl df-juxt df-encl llq df-encl llr df-encl df-juxt llp
    df-encl df-juxt df-encl lls df-encl llp df-encl df-juxt df-encl df-juxt llp
    df-encl llq df-encl df-juxt llr df-encl df-juxt df-encl llp df-encl lls
    df-encl df-juxt df-encl df-juxt llq df-encl llr df-encl df-juxt lls llp
    df-encl c7 llq df-encl llr df-encl df-juxt llp df-encl df-juxt df-encl llp
    df-encl llq df-encl df-juxt llr df-encl df-juxt df-encl lls df-encl llp
    df-encl df-juxt df-encl llp df-encl lls df-encl df-juxt df-encl llq df-encl
    llr df-encl df-juxt llp df-encl df-void df-void df-void df-void df-void
    cmmbx lls df-encl llp df-encl df-void df-void df-void df-void df-void cmmbx
    quad tran tran $.

  $( Crosstransposition.  Theorem C9 of [Spencer-Brown] p. 35.  (Contributed by
     Naip Moro, 6-Sep-2015.) $)
  c9 $p |- [ [ [ q ] [ p ] ] [ [ r ] [ p ] ] [ [ s ] p ] [ [ t ] p ] ]
             = [ [ p ] q r ] [ p s t ] $=
    llq df-encl llp df-encl df-juxt df-encl llr df-encl llp df-encl df-juxt
    df-encl df-juxt lls df-encl llp df-juxt df-encl df-juxt llt df-encl llp
    df-juxt df-encl df-juxt df-encl lls llt df-juxt df-encl llp df-juxt df-encl
    llq df-encl llp df-encl df-juxt df-encl df-juxt llr df-encl llp df-encl
    df-juxt df-encl df-juxt df-encl llp df-encl llq df-juxt llr df-juxt df-encl
    llp lls df-juxt llt df-juxt df-encl df-juxt lls df-encl llp df-juxt df-encl
    llt df-encl llp df-juxt df-encl df-juxt lls llt df-juxt df-encl llp df-juxt
    df-encl llq df-encl llp df-encl df-juxt df-encl llr df-encl llp df-encl
    df-juxt df-encl df-juxt df-void df-void df-void lls df-encl llp df-juxt
    df-encl llt df-encl llp df-juxt df-encl df-juxt df-encl df-encl lls df-encl
    llp df-juxt df-encl llt df-encl llp df-juxt df-encl df-juxt lls llt df-juxt
    df-encl llp df-juxt df-encl lls df-encl llp df-juxt df-encl llt df-encl llp
    df-juxt df-encl df-juxt c1 lls df-encl llp df-juxt df-encl llt df-encl llp
    df-juxt df-encl df-juxt df-encl lls llt df-juxt df-encl llp df-juxt lls
    df-encl llp df-juxt df-encl llt df-encl llp df-juxt df-encl df-juxt df-encl
    lls df-encl df-encl llt df-encl df-encl df-juxt df-encl llp df-juxt lls llt
    df-juxt df-encl llp df-juxt lls df-encl llt df-encl llp ax-j2 lls df-encl
    df-encl lls llt df-encl df-encl llt df-void df-void df-void df-void llp lls
    c1 llt c1 quadbx tran beq eucr subb2 lls llt df-juxt df-encl llp df-juxt
    df-encl llq df-encl llp df-encl df-juxt df-encl df-juxt llr df-encl llp
    df-encl df-juxt df-encl df-juxt df-encl lls llt df-juxt df-encl llp df-juxt
    df-encl llq df-juxt llr df-juxt df-encl lls llt df-juxt llp df-juxt df-encl
    df-juxt llp df-encl llq df-juxt llr df-juxt df-encl llp lls df-juxt llt
    df-juxt df-encl df-juxt lls llt df-juxt df-encl llp df-juxt df-encl llq
    df-encl llp df-encl df-juxt df-encl df-juxt llr df-encl llp df-encl df-juxt
    df-encl df-juxt df-encl lls llt df-juxt df-encl llp df-juxt df-encl llq
    df-juxt llr df-juxt df-encl lls llt df-juxt df-encl df-encl llp df-juxt
    df-encl df-juxt lls llt df-juxt df-encl llp df-juxt df-encl llq df-juxt llr
    df-juxt df-encl lls llt df-juxt llp df-juxt df-encl df-juxt lls llt df-juxt
    df-encl llp df-juxt df-encl llq df-encl llp df-encl df-juxt df-encl df-juxt
    llr df-encl llp df-encl df-juxt df-encl df-juxt df-encl lls llt df-juxt
    df-encl llp df-juxt df-encl llq df-juxt llr df-juxt df-encl lls llt df-juxt
    df-encl llp df-juxt df-encl llp df-juxt df-encl df-juxt lls llt df-juxt
    df-encl llp df-juxt df-encl llq df-juxt llr df-juxt df-encl lls llt df-juxt
    df-encl df-encl llp df-juxt df-encl df-juxt lls llt df-juxt df-encl llp
    df-juxt df-encl llq df-encl llp df-encl df-juxt df-encl df-juxt llr df-encl
    llp df-encl df-juxt df-encl df-juxt df-encl lls llt df-juxt df-encl llp
    df-juxt df-encl llq df-juxt llr df-juxt df-encl lls llt df-juxt df-encl llp
    df-juxt df-encl llp df-encl df-encl df-juxt df-encl df-juxt lls llt df-juxt
    df-encl llp df-juxt df-encl llq df-juxt llr df-juxt df-encl lls llt df-juxt
    df-encl llp df-juxt df-encl llp df-juxt df-encl df-juxt lls llt df-juxt
    df-encl llp df-juxt df-encl llq df-encl llp df-encl df-juxt df-encl df-juxt
    llr df-encl llp df-encl df-juxt df-encl df-juxt df-encl lls llt df-juxt
    df-encl llp df-juxt df-encl llq df-encl df-encl df-juxt llr df-encl df-encl
    df-juxt df-encl lls llt df-juxt df-encl llp df-juxt df-encl llp df-encl
    df-encl df-juxt df-encl df-juxt lls llt df-juxt df-encl llp df-juxt df-encl
    llq df-juxt llr df-juxt df-encl lls llt df-juxt df-encl llp df-juxt df-encl
    llp df-encl df-encl df-juxt df-encl df-juxt lls llt df-juxt df-encl llp
    df-juxt llq df-encl llr df-encl llp df-encl c8 llq df-encl df-encl llq llr
    df-encl df-encl llr lls llt df-juxt df-encl llp df-juxt df-encl df-void
    df-void df-void lls llt df-juxt df-encl llp df-juxt df-encl llp df-encl
    df-encl df-juxt df-encl llq c1 llr c1 quadbx tran llp df-encl df-encl llp
    lls llt df-juxt df-encl llp df-juxt df-encl df-void lls llt df-juxt df-encl
    llp df-juxt df-encl llq df-juxt llr df-juxt df-encl df-void llp c1 subb1
    tran lls llt df-juxt df-encl llp df-juxt df-encl llp df-juxt lls llt
    df-juxt df-encl df-encl llp df-juxt df-void df-void lls llt df-juxt df-encl
    llp df-juxt df-encl llq df-juxt llr df-juxt df-encl df-void lls llt df-juxt
    df-encl llp c2 subb1 tran lls llt df-juxt df-encl df-encl lls llt df-juxt
    df-void llp lls llt df-juxt df-encl llp df-juxt df-encl llq df-juxt llr
    df-juxt df-encl df-void lls llt df-juxt c1 subb1 tran lls llt df-juxt
    df-encl llp df-juxt df-encl llq df-juxt llr df-juxt lls llt df-juxt llp
    df-juxt df-encl df-juxt df-encl lls llt df-juxt llp df-juxt df-encl df-juxt
    lls llt df-juxt df-encl llp df-juxt df-encl llq df-juxt llr df-juxt df-encl
    lls llt df-juxt llp df-juxt df-encl df-juxt llp df-encl llq df-juxt llr
    df-juxt df-encl llp lls df-juxt llt df-juxt df-encl df-juxt lls llt df-juxt
    df-encl llp df-juxt df-encl llq df-juxt llr df-juxt lls llt df-juxt llp
    df-juxt df-encl c2 lls llt df-juxt df-encl llp df-juxt df-encl llq df-juxt
    llr df-juxt lls llt df-juxt llp df-juxt df-encl df-juxt df-encl lls llt
    df-juxt llp df-juxt df-encl df-juxt llp lls llt df-juxt df-encl df-juxt
    df-encl llq df-juxt llr df-juxt llp lls df-juxt llt df-juxt df-encl df-juxt
    df-encl lls llt df-juxt llp df-juxt df-encl df-juxt llp df-encl llq df-juxt
    llr df-juxt df-encl llp lls df-juxt llt df-juxt df-encl df-juxt lls llt
    df-juxt df-encl llp df-juxt df-encl llp lls llt df-juxt df-encl df-juxt
    df-encl lls llt df-juxt llp df-juxt df-encl llp lls df-juxt llt df-juxt
    df-encl df-void llq llr df-juxt df-void df-void lls llt df-juxt llp df-juxt
    df-encl lls llt df-juxt df-encl llp df-void df-void df-void df-void df-void
    cmmbx lls llt df-juxt llp df-void df-void df-void df-void df-void cmmbx
    quadbx llp df-encl df-encl lls llt df-juxt df-encl df-juxt df-encl llq
    df-juxt llr df-juxt llp df-encl df-encl lls df-juxt llt df-juxt df-encl
    df-juxt df-encl lls llt df-juxt llp df-juxt df-encl df-juxt llp lls llt
    df-juxt df-encl df-juxt df-encl llq df-juxt llr df-juxt llp lls df-juxt llt
    df-juxt df-encl df-juxt df-encl lls llt df-juxt llp df-juxt df-encl df-juxt
    llp df-encl llq df-juxt llr df-juxt df-encl llp lls df-juxt llt df-juxt
    df-encl df-juxt llp df-encl df-encl lls llt df-juxt df-encl df-juxt df-encl
    llq df-juxt llr df-juxt llp lls llt df-juxt df-encl df-juxt df-encl llq
    df-juxt llr df-juxt llp df-encl df-encl lls df-juxt llt df-juxt df-encl llp
    lls df-juxt llt df-juxt df-encl df-void df-void df-void df-void lls llt
    df-juxt llp df-juxt df-encl llp df-encl df-encl llp df-void lls llt df-juxt
    df-encl df-void llq llr df-juxt llp c1 subb1 llp df-encl df-encl llp
    df-void lls llt df-juxt df-void df-void llp c1 subb1 quadbx llp df-encl
    df-encl lls llt df-juxt df-encl df-juxt df-encl llq df-juxt llr df-juxt llp
    df-encl df-encl lls df-juxt llt df-juxt df-encl df-juxt df-encl lls llt
    df-juxt llp df-juxt df-encl df-juxt llp df-encl df-encl lls llt df-juxt
    df-encl df-juxt df-encl llp df-encl df-encl lls df-juxt llt df-juxt df-encl
    df-juxt llq df-juxt llr df-juxt df-encl lls llt df-juxt llp df-juxt df-encl
    df-juxt llp df-encl llq df-juxt llr df-juxt df-encl llp lls df-juxt llt
    df-juxt df-encl df-juxt llq llr df-juxt llp df-encl df-encl lls df-juxt llt
    df-juxt df-encl llp df-encl df-encl lls llt df-juxt df-encl df-juxt df-encl
    df-void df-void df-void lls llt df-juxt llp df-juxt df-encl cmmbx llp
    df-encl df-encl lls llt df-juxt df-encl df-juxt df-encl llp df-encl df-encl
    lls df-juxt llt df-juxt df-encl df-juxt llq df-juxt llr df-juxt df-encl lls
    llt df-juxt llp df-juxt df-encl df-juxt llp df-encl llq df-juxt llr df-juxt
    df-encl lls llt df-juxt llp df-juxt df-encl df-juxt llp df-encl llq df-juxt
    llr df-juxt df-encl llp lls df-juxt llt df-juxt df-encl df-juxt llp df-encl
    df-encl lls llt df-juxt df-encl df-juxt df-encl llp df-encl df-encl lls
    df-juxt llt df-juxt df-encl df-juxt llp df-encl df-void llq llr df-juxt
    df-void lls llt df-juxt llp df-juxt df-encl llp df-encl lls llt df-juxt c6
    subb1 lls llt df-juxt llp df-void df-void df-void llp df-encl llq df-juxt
    llr df-juxt df-encl df-void cmmbx tran tran eucr tran eucr tran tran     $.

  $( The following two equations (or rules of calculation) constitute the
     entire Primary Arithmetic which underlies the Primary Algebra, so are
     conceptually prior to the axioms and theorems.  LoF, and hence
     propositional logic, is nothing but a prolonged deduction from this pair
     of arithmetical identities.
  $)

  $( Number.  Rule I1 of [Spencer-Brown] p. 12.  (Contributed by Naip Moro,
     14-Feb-2017.) $)
  i1 $p |- [ ] [ ] = [ ] $=
    df-void df-encl c5 $.

  $( Order.  Rule I2 of [Spencer-Brown] p. 12.  (Contributed by Naip Moro,
     14-Feb-2017.) $)
  i2 $p |- [ [ ] ] = $=
    df-void ax-j1 $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                    9. Generalizations of LoF propositions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This section is a modest start to ease the pain of calculating with LoF in a
  one-dimensional notation.  In generalizing some major theorems, it attempts
  to lighten the significant overhead of commutative term rearrangements and
  maintenance of equational symmetries.  The ugliness of the section is a gauge
  of how inappropriate linear notations are to LoF.
$)

  $( Generalizations of C1. $)

  $( c1 reversed.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  c1r $p |- p = [ [ p ] ] $=
    llp df-encl df-encl llp llp c1 sym $.

  $( c1 extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  c1x $p |- u [ [ p ] ] v = u p v $=
    llp df-encl df-encl llp llu llv llp c1 subst $.

  $( c1 reversed and extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  c1rx $p |- u p v = u [ [ p ] ] v $=
    llp llp df-encl df-encl llu llv llp c1r subst $.

  $( c1 bounded and extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  c1bx $p |- w [ u [ [ p ] ] v ] x = w [ u p v ] x $=
    llu llp df-encl df-encl df-juxt llv df-juxt llu llp df-juxt llv df-juxt
    df-void df-void llw llx llp llu llv c1x subb1 $.

  $( c1 reversed, bounded, and extended.  (Contributed by Naip Moro,
     14-Feb-2017.) $)
  c1rbx $p |- w [ u p v ] x = w [ u [ [ p ] ] v ] x $=
    llw llu llp df-encl df-encl df-juxt llv df-juxt df-encl df-juxt llx df-juxt
    llw llu llp df-juxt llv df-juxt df-encl df-juxt llx df-juxt llp llu llv llw
    llx c1bx sym $.

  $( Generalizations of C2. $)

  $( c2 extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  c2x $p |- u [ p q v ] w q x = u [ p v ] w q x $=
    llu llp llv df-juxt df-encl df-juxt llw df-juxt llq df-juxt llx df-juxt llu
    llp llq df-juxt llv df-juxt df-encl df-juxt llw df-juxt llq df-juxt llx
    df-juxt llq llw df-juxt llw llq df-juxt llu llp llv df-juxt df-encl df-juxt
    llx llu llp llq df-juxt llv df-juxt df-encl df-juxt llw df-juxt llq df-juxt
    llx df-juxt llq llw cmm llp llv df-juxt llq df-juxt df-encl llq df-juxt llp
    llv df-juxt df-encl llq df-juxt llu llw llx df-juxt llu llp llq df-juxt llv
    df-juxt df-encl df-juxt llw df-juxt llq df-juxt llx df-juxt llp llv df-juxt
    llq c2 llu llp llq df-juxt llv df-juxt df-encl df-juxt llw df-juxt llq
    df-juxt llx df-juxt llu llp llv df-juxt llq df-juxt df-encl df-juxt llq
    df-juxt llw df-juxt llx df-juxt llu llp llq df-juxt llv df-juxt df-encl
    df-juxt llw df-juxt llq df-juxt llx df-juxt llu llp llv df-juxt llq df-juxt
    df-encl df-juxt llw df-juxt llq df-juxt llx df-juxt llu llp llv df-juxt llq
    df-juxt df-encl df-juxt llq df-juxt llw df-juxt llx df-juxt llq llv llp
    df-void df-void llu llw llq df-juxt llx df-juxt cmmbx llw llq llu llp llv
    df-juxt llq df-juxt df-encl df-juxt df-void llx cmmx tran sym rep rep sym
    $.

  $( c2 bounded and extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  c2bx $p |- y [ u [ p q v ] w q x ] z = y [ u [ p v ] w q x ] z $=
    llu llp llq df-juxt llv df-juxt df-encl df-juxt llw df-juxt llq df-juxt llx
    df-juxt llu llp llv df-juxt df-encl df-juxt llw df-juxt llq df-juxt llx
    df-juxt df-void df-void lly llz llp llq llu llv llw llx c2x subb1 $.

  $( c2 reversed and extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  c2rx $p |- u q v [ p q w ] x = u q v [ p w ] x $=
    llu llq df-juxt llv df-juxt llp llq df-juxt llw df-juxt df-encl df-juxt llx
    df-juxt llu llp llw df-juxt df-encl df-juxt llq df-juxt llv df-juxt llx
    df-juxt llu llq df-juxt llv df-juxt llp llw df-juxt df-encl df-juxt llx
    df-juxt llu llq df-juxt llv df-juxt llp llq df-juxt llw df-juxt df-encl
    df-juxt llx df-juxt llu llp llq df-juxt llw df-juxt df-encl df-juxt llq
    df-juxt llv df-juxt llx df-juxt llu llp llw df-juxt df-encl df-juxt llq
    df-juxt llv df-juxt llx df-juxt llq llv df-juxt llp llq df-juxt llw df-juxt
    df-encl llu df-void llx cmmx llp llq llu llw df-void llv llx df-juxt c2x
    tran llp llw df-juxt df-encl llq llv df-juxt llu df-void llx cmmx tran $.

  $( c2 reversed, bounded, and extended.  (Contributed by Naip Moro,
     14-Feb-2017.) $)
  c2rbx $p |- y [ u [ p v ] w q x ] z = y [ u [ p q v ] w q x ] z $=
    lly llu llp llq df-juxt llv df-juxt df-encl df-juxt llw df-juxt llq df-juxt
    llx df-juxt df-encl df-juxt llz df-juxt lly llu llp llv df-juxt df-encl
    df-juxt llw df-juxt llq df-juxt llx df-juxt df-encl df-juxt llz df-juxt llp
    llq llu llv llw llx lly llz c2bx sym $.

  $( c2 special case.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  c2e $p |- u [ p ] v p w = [ ] $=
    llu llp df-encl df-juxt llv df-juxt llp df-juxt llw df-juxt llu df-void
    df-encl df-juxt llv df-juxt llp df-juxt llw df-juxt df-void df-encl df-void
    llp llu df-void llv llw c2x llu df-void df-encl df-juxt llv df-juxt llp
    df-juxt llw df-juxt df-void df-encl llu df-juxt llv df-juxt llp df-juxt llw
    df-juxt df-void df-encl llu df-void df-encl df-void df-void llv llp df-juxt
    llw df-juxt cmmx llu llv df-juxt llp df-juxt llw df-juxt c3 tran tran $.

  $( Generalizations of C3. $)

  $( c3 extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  c3x $p |- p [ ] q = [ ] $=
    llp df-void df-encl df-juxt llq df-juxt df-void df-encl llq df-juxt llp
    df-juxt df-void df-encl llp df-void df-encl llq df-juxt cmm llq llp df-juxt
    c3 tran $.

  $( c3 bounded and extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  c3bx $p |- u [ p [ ] q ] v = u v $=
    llu llp df-void df-encl df-juxt llq df-juxt df-encl df-juxt llv df-juxt llu
    df-void df-encl df-encl df-juxt llv df-juxt llu llv df-juxt llp df-void
    df-encl df-juxt llq df-juxt df-void df-encl df-void df-void llu llv llp llq
    c3x subb1 df-void llu llv c1x tran $.

  $( Generalizations of C4. $)

  $( c4 extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  c4x $p |- w [ u [ p ] v ] x p y = w p x y $=
    llw llu llp df-encl df-juxt llv df-juxt df-encl df-juxt llx df-juxt llp
    df-juxt lly df-juxt llw llp df-encl llu df-juxt llv df-juxt df-encl df-juxt
    llp df-juxt llx df-juxt lly df-juxt llw llp df-juxt llx df-juxt lly df-juxt
    llw llu llp df-encl df-juxt llv df-juxt df-encl df-juxt llx df-juxt llp
    df-juxt lly df-juxt llw llp df-encl llu df-juxt llv df-juxt df-encl df-juxt
    llx df-juxt llp df-juxt lly df-juxt llw llp df-encl llu df-juxt llv df-juxt
    df-encl df-juxt llp df-juxt llx df-juxt lly df-juxt llu llp df-encl df-void
    df-void llv llw llx llp df-juxt lly df-juxt cmmbx llx llp llw llp df-encl
    llu df-juxt llv df-juxt df-encl df-juxt df-void lly cmmx tran llp df-encl
    llu df-juxt llv df-juxt df-encl llp df-juxt llp llw llx lly df-juxt llw llp
    df-encl llu df-juxt llv df-juxt df-encl df-juxt llp df-juxt llx df-juxt lly
    df-juxt llp llu llv df-juxt c4 llw llp df-encl llu df-juxt llv df-juxt
    df-encl df-juxt llp df-juxt llx df-juxt lly df-juxt id rep euc $.

  $( c4 reversed and extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  c4rx $p |- w p x y = w [ u [ p ] v ] x p y $=
    llw llu llp df-encl df-juxt llv df-juxt df-encl df-juxt llx df-juxt llp
    df-juxt lly df-juxt llw llp df-juxt llx df-juxt lly df-juxt llp llu llv llw
    llx lly c4x sym $.

  $( Generalizations of C5. $)

  $( c5 extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  c5x $p |- u p v p w = u p v w $=
    llu llp df-juxt llv df-juxt llp df-juxt llw df-juxt llu llp df-juxt llp
    df-juxt llv df-juxt llw df-juxt llu llp df-juxt llv df-juxt llw df-juxt llv
    llp llu llp df-juxt df-void llw cmmx llp llp df-juxt llp llu llv llw
    df-juxt llu llp df-juxt llp df-juxt llv df-juxt llw df-juxt llp c5 llu llp
    df-juxt llp df-juxt llv df-juxt llw df-juxt id rep euc $.

  $( c5 bounded and extended.  (Contributed by Naip Moro, 25-Feb-2017.) $)
  c5bx $p |- x [ u p v p w ] y = x [ u p v w ] y $=
    llu llp df-juxt llv df-juxt llp df-juxt llw df-juxt llu llp df-juxt llv
    df-juxt llw df-juxt df-void df-void llx lly llp llu llv llw c5x subb1 $.

  $( c5 reversed and extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  c5rx $p |- u p v w = u p v p w $=
    llu llp df-juxt llv df-juxt llp df-juxt llw df-juxt llu llp df-juxt llv
    df-juxt llw df-juxt llp llu llv llw c5x sym $.

  $( Generalizations of C6. $)

  $( c6 extended.  (Contributed by Naip Moro, 25-Feb-2017.) $)
  c6x $p |- u [ [ p ] [ q ] ] v [ [ p ] q ] w = u p v w $=
    llp df-encl llq df-encl df-juxt df-encl llp df-encl llq df-juxt df-encl
    df-juxt llp llu llv llw df-juxt llu llp df-encl llq df-encl df-juxt df-encl
    df-juxt llv df-juxt llp df-encl llq df-juxt df-encl df-juxt llw df-juxt llp
    llq c6 llv llp df-encl llq df-juxt df-encl llu llp df-encl llq df-encl
    df-juxt df-encl df-juxt df-void llw cmmx reps $.

  $( c6 reversed and extended.  (Contributed by Naip Moro, 25-Feb-2017.) $)
  c6rx $p |- u [ [ p ] q ] v [ [ p ] [ q ] ] w = u p v w $=
    llu llp df-encl llq df-juxt df-encl df-juxt llv df-juxt llp df-encl llq
    df-encl df-juxt df-encl df-juxt llw df-juxt llu llp df-encl llq df-encl
    df-juxt df-encl df-juxt llv df-juxt llp df-encl llq df-juxt df-encl df-juxt
    llw df-juxt llu llp df-juxt llv df-juxt llw df-juxt llp df-encl llq df-juxt
    df-encl llp df-encl llq df-encl df-juxt df-encl llu llv llw cmmx llp llq
    llu llv llw c6x tran $.

  $( Generalizations of J1. $)

  $( ax-j1 extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  j1x $p |- x [ u [ p ] v p w ] y = x y $=
    llx llu llp df-encl df-juxt llv df-juxt llp df-juxt llw df-juxt df-encl
    df-juxt lly df-juxt llx llu df-void df-encl df-juxt llv df-juxt llp df-juxt
    llw df-juxt df-encl df-juxt lly df-juxt llx lly df-juxt df-void llp llu
    df-void llv llw llx lly c2bx llu llv llp df-juxt llw df-juxt llx lly c3bx
    tran $.

  $( ax-j1 reversed and extended.  (Contributed by Naip Moro,
     25-Feb-2017.) $)
  j1rx $p |- x [ u p v [ p ] w ] y = x y $=
    llx llu llp df-juxt llv df-juxt llp df-encl df-juxt llw df-juxt df-encl
    df-juxt lly df-juxt llx llu llp df-encl df-juxt llv df-juxt llp df-juxt llw
    df-juxt df-encl df-juxt lly df-juxt llx lly df-juxt llp llp df-encl llu llv
    llw llx lly cmmbx llp llu llv llw llx lly j1x tran $.

  $( ax-j1 extended and switched.  (Contributed by Naip Moro,
     14-Feb-2017.) $)
  j1xs $p |- x y = x [ u [ p ] v p w ] y $=
    llx llu llp df-encl df-juxt llv df-juxt llp df-juxt llw df-juxt df-encl
    df-juxt lly df-juxt llx lly df-juxt llp llu llv llw llx lly j1x sym $.

  $( Generalizations of J2. $)

  $( ax-j2 extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  j2x $p |- u [ [ p r ] [ q r ] ] v w = u [ [ p ] [ q ] ] v r w $=
    llu llp llr df-juxt df-encl llq llr df-juxt df-encl df-juxt df-encl df-juxt
    llv df-juxt llw df-juxt llu llp df-encl llq df-encl df-juxt df-encl df-juxt
    llr df-juxt llv df-juxt llw df-juxt llu llp df-encl llq df-encl df-juxt
    df-encl df-juxt llv df-juxt llr df-juxt llw df-juxt llp llr df-juxt df-encl
    llq llr df-juxt df-encl df-juxt df-encl llp df-encl llq df-encl df-juxt
    df-encl llr df-juxt llu llv llw df-juxt llp llq llr ax-j2 subst llr llv llu
    llp df-encl llq df-encl df-juxt df-encl df-juxt df-void llw cmmx tran $.

  $( ax-j2 reversed and extended.  (Contributed by Naip Moro,
     14-Feb-2017.) $)
  j2rx $p |- u [ [ p ] [ q ] ] v r w = u [ [ p r ] [ q r ] ] v w $=
    llu llp llr df-juxt df-encl llq llr df-juxt df-encl df-juxt df-encl df-juxt
    llv df-juxt llw df-juxt llu llp df-encl llq df-encl df-juxt df-encl df-juxt
    llv df-juxt llr df-juxt llw df-juxt llp llq llr llu llv llw j2x sym $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                          10. Excursion into equality
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( We will later define ( p -> q ) as [ p ] q .  In that light, this theorem
     shows that our previous definition of equality is equivalent to
     ( ( p -> q ) /\ ( q -> p ) ) .  The latter, in turn, is what we
     mean by the biconditional <-> .  In other words, equality and the
     biconditional are, as expected, equivalent.  (Contributed by Naip Moro,
     24-Feb-2017.) $)
  biimp $p |- [ [ [ p ] q ] [ [ q ] p ] ] = [ [ p ] [ q ] ] [ p q ] $=
    llq llp df-encl df-juxt df-encl llq df-encl llp df-juxt df-encl df-juxt
    df-encl llp df-encl llq df-juxt df-encl llq df-encl llp df-juxt df-encl
    df-juxt df-encl llp df-encl llq df-encl df-juxt df-encl llp llq df-juxt
    df-encl df-juxt llq llp df-encl df-juxt llp df-encl llq df-juxt df-void
    df-void df-void llq df-encl llp df-juxt df-encl df-void df-void llq llp
    df-encl cmm subbd1 llq df-encl df-encl llp df-encl df-juxt df-encl llq
    df-encl llp df-juxt df-encl df-juxt df-encl llq llp df-encl df-juxt df-encl
    llq df-encl llp df-juxt df-encl df-juxt df-encl llp df-encl llq df-encl
    df-juxt df-encl llp llq df-juxt df-encl df-juxt llq df-encl df-encl llq
    df-void llp df-encl df-void llq df-encl llp df-juxt df-encl df-void df-void
    llq c1 subbd1 df-void df-encl llp df-encl df-juxt df-encl df-void df-encl
    llp df-juxt df-encl df-juxt llq df-encl df-encl llp df-encl df-juxt df-encl
    df-juxt llq df-encl llp df-juxt df-encl df-juxt df-encl llq df-encl df-encl
    llp df-encl df-juxt df-encl llq df-encl llp df-juxt df-encl df-juxt df-encl
    llp df-encl llq df-encl df-juxt df-encl llp llq df-juxt df-encl df-juxt
    df-void df-encl llp df-encl df-juxt df-encl df-void df-encl llp df-juxt
    df-encl df-juxt df-void df-void llq df-encl df-encl llp df-encl df-juxt
    df-encl llq df-encl llp df-juxt df-encl df-juxt df-void df-void df-void llp
    c6 subb1 df-void df-encl llp df-encl df-juxt df-encl llq df-encl df-encl
    llp df-encl df-juxt df-encl df-juxt llq df-encl llp df-juxt df-encl df-juxt
    df-void df-encl llp df-juxt df-encl df-juxt df-encl df-void df-encl llp
    df-encl df-juxt df-encl df-void df-encl llp df-juxt df-encl df-juxt llq
    df-encl df-encl llp df-encl df-juxt df-encl df-juxt llq df-encl llp df-juxt
    df-encl df-juxt df-encl llp df-encl llq df-encl df-juxt df-encl llp llq
    df-juxt df-encl df-juxt llq df-encl df-encl llp df-encl df-juxt df-encl llq
    df-encl llp df-juxt df-encl df-juxt df-void df-encl llp df-juxt df-encl
    df-void df-encl llp df-encl df-juxt df-encl df-void df-void df-void df-void
    cmmbx llp df-void llq df-encl llq df-void c9 eucr eucr eucr eucr $.

  $( We next prove that equality, and hence the biconditional, are associative.
     First, four preliminary theorems. $)

  $( Lemma.  (Contributed by Naip Moro, 24-Feb-2017.) $)
  biasslem1 $p |- [ q [ p q ] r ] = [ [ p ] q r ] $=
    llq llp llq df-juxt df-encl df-juxt llr df-juxt df-encl llp llq df-juxt
    df-encl llq df-juxt llr df-juxt df-encl llp df-encl llq df-juxt llr df-juxt
    df-encl llq llp llq df-juxt df-encl df-void df-void llr df-void df-void
    cmmbx llp llq df-void df-void df-void llr df-void df-void c2bx tran $.

  $( Lemma.  (Contributed by Naip Moro, 24-Feb-2017.) $)
  biasslem2 $p |- [ p [ p q ] r ] = [ p [ q ] r ] $=
    llp llp llq df-juxt df-encl df-juxt llr df-juxt df-encl llq df-encl llp
    df-juxt llr df-juxt df-encl llp llq df-encl df-juxt llr df-juxt df-encl llp
    llp llq df-juxt df-encl df-juxt llr df-juxt df-encl llp llq llp df-juxt
    df-encl df-juxt llr df-juxt df-encl llq df-encl llp df-juxt llr df-juxt
    df-encl llp llq df-void df-void df-void llp llr df-void df-void cmmbdx llq
    llp llr biasslem1 tran llq df-encl llp df-void df-void llr df-void df-void
    cmmbx tran $.

  $( Let P = [ [ p ] [ q ] ] [ p q ] and Q = [ [ q ] [ r ] ] [ q r ] .  Proving
     that equality/biconditional associates amounts to proving:
     [ [ P ] [ r ] ] [ P r ] = [ [ p ] [ Q ] ] [ p Q ] which is demonstrated in
     'biass'.  Meanwhile, this theorem shows that the lhs of the latter
     equation evaluates to a form symmetric in the three variables, informal
     evidence for associativity.  (Contributed by Naip Moro, 24-Feb-2017.) $)
  biass3 $p |- [ [ [ [ p ] [ q ] ] [ p q ] ] [ r ] ]
               [ [ [ p ] [ q ] ] [ p q ] r ]
                  = [ [ p ] [ q ] [ r ] ] [ p q [ r ] ]
                    [ p [ q ] r ] [ [ p ] q r ] $=
    llp df-encl llq df-encl df-juxt df-encl llp llq df-juxt df-encl df-juxt
    df-encl llr df-encl df-juxt df-encl llp df-encl llq df-encl df-juxt df-encl
    llp llq df-juxt df-encl df-juxt llr df-juxt df-encl df-juxt llp df-encl llq
    df-encl df-juxt llr df-encl df-juxt df-encl llp llq df-juxt llr df-encl
    df-juxt df-encl df-juxt llp llq df-encl df-juxt llr df-juxt df-encl df-juxt
    llq llp llq df-juxt df-encl df-juxt llr df-juxt df-encl df-juxt llp df-encl
    llq df-encl df-juxt llr df-encl df-juxt df-encl llp llq df-juxt llr df-encl
    df-juxt df-encl df-juxt llp llq df-encl df-juxt llr df-juxt df-encl df-juxt
    llp df-encl llq df-juxt llr df-juxt df-encl df-juxt llp df-encl llq df-encl
    df-juxt df-encl llp llq df-juxt df-encl df-juxt df-encl llr df-encl df-juxt
    df-encl llp df-encl llq df-encl df-juxt df-encl llp llq df-juxt df-encl
    df-juxt llr df-juxt df-encl df-juxt llp df-encl llq df-encl df-juxt llr
    df-encl df-juxt df-encl llp llq df-juxt llr df-encl df-juxt df-encl df-juxt
    llp llp llq df-juxt df-encl df-juxt llr df-juxt df-encl llq llp llq df-juxt
    df-encl df-juxt llr df-juxt df-encl df-juxt df-juxt llp df-encl llq df-encl
    df-juxt llr df-encl df-juxt df-encl llp llq df-juxt llr df-encl df-juxt
    df-encl df-juxt llp llq df-encl df-juxt llr df-juxt df-encl llq llp llq
    df-juxt df-encl df-juxt llr df-juxt df-encl df-juxt df-juxt llp df-encl llq
    df-encl df-juxt df-encl llp llq df-juxt df-encl df-juxt df-encl llr df-encl
    df-juxt df-encl llp df-encl llq df-encl df-juxt llr df-encl df-juxt df-encl
    llp llq df-juxt llr df-encl df-juxt df-encl df-juxt llp df-encl llq df-encl
    df-juxt df-encl llp llq df-juxt df-encl df-juxt llr df-juxt df-encl llp llp
    llq df-juxt df-encl df-juxt llr df-juxt df-encl llq llp llq df-juxt df-encl
    df-juxt llr df-juxt df-encl df-juxt llp df-encl llq df-encl df-juxt llr
    df-encl df-juxt df-encl llp llq df-juxt llr df-encl df-juxt df-encl df-juxt
    df-encl df-encl llp df-encl llq df-encl df-juxt df-encl llp llq df-juxt
    df-encl df-juxt df-encl llr df-encl df-juxt df-encl llp df-encl llq df-encl
    df-juxt llr df-encl df-juxt df-encl llp llq df-juxt llr df-encl df-juxt
    df-encl df-juxt llp df-encl llq df-encl df-juxt llr df-encl df-juxt df-encl
    llp llq df-juxt llr df-encl df-juxt df-encl df-juxt df-encl llp df-encl llq
    df-encl df-juxt df-encl llp llq df-juxt df-encl df-juxt df-encl llr df-encl
    df-juxt llp df-encl llq df-encl df-juxt llp llq df-juxt llr df-encl ax-j2
    beq llp df-encl llq df-encl df-juxt llr df-encl df-juxt df-encl llp llq
    df-juxt llr df-encl df-juxt df-encl df-juxt c1 eucr llp llp llq df-juxt
    df-encl df-juxt llr df-juxt df-encl llq llp llq df-juxt df-encl df-juxt llr
    df-juxt df-encl df-juxt df-encl df-encl llp df-encl llq df-encl df-juxt
    df-encl llp llq df-juxt df-encl df-juxt llr df-juxt df-encl llp llp llq
    df-juxt df-encl df-juxt llr df-juxt df-encl llq llp llq df-juxt df-encl
    df-juxt llr df-juxt df-encl df-juxt llp llp llq df-juxt df-encl df-juxt llr
    df-juxt df-encl llq llp llq df-juxt df-encl df-juxt llr df-juxt df-encl
    df-juxt df-encl llp df-encl llq df-encl df-juxt df-encl llp llq df-juxt
    df-encl df-juxt llr df-juxt llp llq llp llq df-juxt df-encl llr df-juxt
    ax-j2 beq llp llp llq df-juxt df-encl df-juxt llr df-juxt df-encl llq llp
    llq df-juxt df-encl df-juxt llr df-juxt df-encl df-juxt c1 eucr quad llp
    llp llq df-juxt df-encl df-juxt llr df-juxt df-encl llp llq df-encl df-juxt
    llr df-juxt df-encl llp df-encl llq df-encl df-juxt llr df-encl df-juxt
    df-encl llp llq df-juxt llr df-encl df-juxt df-encl df-juxt llq llp llq
    df-juxt df-encl df-juxt llr df-juxt df-encl llp llq llr biasslem2 subst
    tran llq llp llq df-juxt df-encl df-juxt llr df-juxt df-encl llp df-encl
    llq df-juxt llr df-juxt df-encl llp df-encl llq df-encl df-juxt llr df-encl
    df-juxt df-encl llp llq df-juxt llr df-encl df-juxt df-encl df-juxt llp llq
    df-encl df-juxt llr df-juxt df-encl df-juxt llp llq llr biasslem1 subr
    tran $.

  $( A permuted version of biass3 .  (Contributed by Naip Moro,
     29-Dec-2016.) $)
  biass3p $p |- [ [ [ [ q ] [ r ] ] [ q r ] ] [ p ] ]
                [ [ [ q ] [ r ] ] [ q r ] p ]
                   = [ [ p ] [ q ] [ r ] ] [ p q [ r ] ]
                     [ p [ q ] r ] [ [ p ] q r ] $=
    llq df-encl llr df-encl df-juxt df-encl llq llr df-juxt df-encl df-juxt
    df-encl llp df-encl df-juxt df-encl llq df-encl llr df-encl df-juxt df-encl
    llq llr df-juxt df-encl df-juxt llp df-juxt df-encl df-juxt llp df-encl llq
    df-encl df-juxt llr df-encl df-juxt df-encl llp df-encl llq df-juxt llr
    df-juxt df-encl df-juxt llp llq df-encl df-juxt llr df-juxt df-encl df-juxt
    llp llq df-juxt llr df-encl df-juxt df-encl df-juxt llp df-encl llq df-encl
    df-juxt llr df-encl df-juxt df-encl llp llq df-juxt llr df-encl df-juxt
    df-encl df-juxt llp llq df-encl df-juxt llr df-juxt df-encl df-juxt llp
    df-encl llq df-juxt llr df-juxt df-encl df-juxt llq df-encl llr df-encl
    df-juxt df-encl llq llr df-juxt df-encl df-juxt df-encl llp df-encl df-juxt
    df-encl llq df-encl llr df-encl df-juxt df-encl llq llr df-juxt df-encl
    df-juxt llp df-juxt df-encl df-juxt llp df-encl llq df-encl df-juxt llr
    df-encl df-juxt df-encl llp df-encl llq df-juxt llr df-juxt df-encl df-juxt
    llp llq df-juxt llr df-encl df-juxt df-encl df-juxt llp llq df-encl df-juxt
    llr df-juxt df-encl df-juxt llp df-encl llq df-encl df-juxt llr df-encl
    df-juxt df-encl llp df-encl llq df-juxt llr df-juxt df-encl df-juxt llp llq
    df-encl df-juxt llr df-juxt df-encl df-juxt llp llq df-juxt llr df-encl
    df-juxt df-encl df-juxt llq df-encl llr df-encl df-juxt df-encl llq llr
    df-juxt df-encl df-juxt df-encl llp df-encl df-juxt df-encl llq df-encl llr
    df-encl df-juxt df-encl llq llr df-juxt df-encl df-juxt llp df-juxt df-encl
    df-juxt llp df-encl llq df-encl df-juxt llr df-encl df-juxt df-encl llp
    df-encl llq df-juxt llr df-juxt df-encl df-juxt llp llq df-juxt llr df-encl
    df-juxt df-encl df-juxt llq df-encl llr df-juxt llp df-juxt df-encl df-juxt
    llp df-encl llq df-encl df-juxt llr df-encl df-juxt df-encl llp df-encl llq
    df-juxt llr df-juxt df-encl df-juxt llp llq df-juxt llr df-encl df-juxt
    df-encl df-juxt llp llq df-encl df-juxt llr df-juxt df-encl df-juxt llq
    df-encl llr df-encl df-juxt df-encl llq llr df-juxt df-encl df-juxt df-encl
    llp df-encl df-juxt df-encl llq df-encl llr df-encl df-juxt df-encl llq llr
    df-juxt df-encl df-juxt llp df-juxt df-encl df-juxt llp df-encl llq df-encl
    df-juxt llr df-encl df-juxt df-encl llp df-encl llq df-juxt llr df-juxt
    df-encl df-juxt llq llr df-encl df-juxt llp df-juxt df-encl df-juxt llq
    df-encl llr df-juxt llp df-juxt df-encl df-juxt llp df-encl llq df-encl
    df-juxt llr df-encl df-juxt df-encl llp df-encl llq df-juxt llr df-juxt
    df-encl df-juxt llp llq df-juxt llr df-encl df-juxt df-encl df-juxt llq
    df-encl llr df-juxt llp df-juxt df-encl df-juxt llq df-encl llr df-encl
    df-juxt df-encl llq llr df-juxt df-encl df-juxt df-encl llp df-encl df-juxt
    df-encl llq df-encl llr df-encl df-juxt df-encl llq llr df-juxt df-encl
    df-juxt llp df-juxt df-encl df-juxt llp df-encl llq df-encl df-juxt llr
    df-encl df-juxt df-encl llq llr df-juxt llp df-encl df-juxt df-encl df-juxt
    llq llr df-encl df-juxt llp df-juxt df-encl df-juxt llq df-encl llr df-juxt
    llp df-juxt df-encl df-juxt llp df-encl llq df-encl df-juxt llr df-encl
    df-juxt df-encl llp df-encl llq df-juxt llr df-juxt df-encl df-juxt llq llr
    df-encl df-juxt llp df-juxt df-encl df-juxt llq df-encl llr df-juxt llp
    df-juxt df-encl df-juxt llq df-encl llr df-encl df-juxt df-encl llq llr
    df-juxt df-encl df-juxt df-encl llp df-encl df-juxt df-encl llq df-encl llr
    df-encl df-juxt df-encl llq llr df-juxt df-encl df-juxt llp df-juxt df-encl
    df-juxt llq df-encl llr df-encl df-juxt llp df-encl df-juxt df-encl llq llr
    df-juxt llp df-encl df-juxt df-encl df-juxt llq llr df-encl df-juxt llp
    df-juxt df-encl df-juxt llq df-encl llr df-juxt llp df-juxt df-encl df-juxt
    llp df-encl llq df-encl df-juxt llr df-encl df-juxt df-encl llq llr df-juxt
    llp df-encl df-juxt df-encl df-juxt llq llr df-encl df-juxt llp df-juxt
    df-encl df-juxt llq df-encl llr df-juxt llp df-juxt df-encl df-juxt llq llr
    llp biass3 llq df-encl llr df-encl df-juxt llp df-encl df-void df-void
    df-void df-void llq llr df-juxt llp df-encl df-juxt df-encl llq llr df-encl
    df-juxt llp df-juxt df-encl df-juxt llq df-encl llr df-juxt llp df-juxt
    df-encl df-juxt cmmbx tran llq llr df-juxt llp df-encl df-void df-void
    df-void llp df-encl llq df-encl df-juxt llr df-encl df-juxt df-encl llq llr
    df-encl df-juxt llp df-juxt df-encl llq df-encl llr df-juxt llp df-juxt
    df-encl df-juxt cmmbx tran llq llr df-encl df-juxt llp df-void df-void
    df-void llp df-encl llq df-encl df-juxt llr df-encl df-juxt df-encl llp
    df-encl llq df-juxt llr df-juxt df-encl df-juxt llq df-encl llr df-juxt llp
    df-juxt df-encl cmmbx tran llq df-encl llr df-juxt llp df-void df-void
    df-void llp df-encl llq df-encl df-juxt llr df-encl df-juxt df-encl llp
    df-encl llq df-juxt llr df-juxt df-encl df-juxt llp llq df-juxt llr df-encl
    df-juxt df-encl df-juxt df-void cmmbx tran llp llq df-juxt llr df-encl
    df-juxt df-encl llp llq df-encl df-juxt llr df-juxt df-encl llp df-encl llq
    df-encl df-juxt llr df-encl df-juxt df-encl llp df-encl llq df-juxt llr
    df-juxt df-encl df-juxt df-void df-void cmmx tran llp df-encl llq df-juxt
    llr df-juxt df-encl llp llq df-juxt llr df-encl df-juxt df-encl llp df-encl
    llq df-encl df-juxt llr df-encl df-juxt df-encl llp llq df-encl df-juxt llr
    df-juxt df-encl df-void cmmx tran $.

  $( Proving the associativity of equality/biconditional.  (Contributed by
     Naip Moro, 29-Dec-2016.) $)
  biass $p |- [ [ [ [ p ] [ q ] ] [ p q ] ] [ r ] ]
              [ [ [ p ] [ q ] ] [ p q ] r ]
                  = [ [ p ] [ [ [ q ] [ r ] ] [ q r ] ] ]
                    [ p [ [ q ] [ r ] ] [ q r ] ] $=
    llp df-encl llq df-encl df-juxt df-encl llp llq df-juxt df-encl df-juxt
    df-encl llr df-encl df-juxt df-encl llp df-encl llq df-encl df-juxt df-encl
    llp llq df-juxt df-encl df-juxt llr df-juxt df-encl df-juxt llq df-encl llr
    df-encl df-juxt df-encl llq llr df-juxt df-encl df-juxt df-encl llp df-encl
    df-juxt df-encl llq df-encl llr df-encl df-juxt df-encl llq llr df-juxt
    df-encl df-juxt llp df-juxt df-encl df-juxt llp df-encl llq df-encl llr
    df-encl df-juxt df-encl llq llr df-juxt df-encl df-juxt df-encl df-juxt
    df-encl llp llq df-encl llr df-encl df-juxt df-encl df-juxt llq llr df-juxt
    df-encl df-juxt df-encl df-juxt llp df-encl llq df-encl df-juxt df-encl llp
    llq df-juxt df-encl df-juxt df-encl llr df-encl df-juxt df-encl llp df-encl
    llq df-encl df-juxt df-encl llp llq df-juxt df-encl df-juxt llr df-juxt
    df-encl df-juxt llp df-encl llq df-encl df-juxt llr df-encl df-juxt df-encl
    llp llq df-juxt llr df-encl df-juxt df-encl df-juxt llp llq df-encl df-juxt
    llr df-juxt df-encl df-juxt llp df-encl llq df-juxt llr df-juxt df-encl
    df-juxt llq df-encl llr df-encl df-juxt df-encl llq llr df-juxt df-encl
    df-juxt df-encl llp df-encl df-juxt df-encl llq df-encl llr df-encl df-juxt
    df-encl llq llr df-juxt df-encl df-juxt llp df-juxt df-encl df-juxt llp llq
    llr biass3 llp llq llr biass3p euc llq df-encl llr df-encl df-juxt df-encl
    llq llr df-juxt df-encl df-juxt df-encl llp df-encl df-juxt df-encl llq
    df-encl llr df-encl df-juxt df-encl llq llr df-juxt df-encl df-juxt llp
    df-juxt df-encl df-juxt llp df-encl llq df-encl llr df-encl df-juxt df-encl
    llq llr df-juxt df-encl df-juxt df-encl df-juxt df-encl llq df-encl llr
    df-encl df-juxt df-encl llq llr df-juxt df-encl df-juxt llp df-juxt df-encl
    df-juxt llp df-encl llq df-encl llr df-encl df-juxt df-encl llq llr df-juxt
    df-encl df-juxt df-encl df-juxt df-encl llp llq df-encl llr df-encl df-juxt
    df-encl df-juxt llq llr df-juxt df-encl df-juxt df-encl df-juxt llq df-encl
    llr df-encl df-juxt df-encl llq llr df-juxt df-encl df-juxt df-encl llp
    df-encl df-void df-void df-void df-void llq df-encl llr df-encl df-juxt
    df-encl llq llr df-juxt df-encl df-juxt llp df-juxt df-encl cmmbx llq
    df-encl llr df-encl df-juxt df-encl llq llr df-juxt df-encl df-juxt llp
    df-void df-void df-void llp df-encl llq df-encl llr df-encl df-juxt df-encl
    llq llr df-juxt df-encl df-juxt df-encl df-juxt df-encl df-void cmmbx tran     tran $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              11.  A bridge between LoF and classical logic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( The Equanimity axiom.  This rule is the key that allows us to switch
     between equational and implicational forms.  $)
  ${
    ax-qny.1 $e |- p $.
    ax-qny.2 $e |- p = q $.
    $( If we assert both p and that p is equal to q, we can infer q.
      (Contributed by Naip Moro, 14-Feb-2017.) $)
    ax-qny $a |- q $.
  $}

  $( This important theorem states that the equivalence of p to True is
     equivalent to just p.  Compare axiom ( A = 1) = A of [Schroeder2] p. 52.
     Schroeder called it "the specific principle of propositional calculus".
     (Contributed by Naip Moro, 29-Jan-2017.) $)
  elimeq $p |- [ [ p ] [ [ ] ] ] [ p [ ] ] = p $=
    llp df-encl df-void df-encl df-encl df-juxt df-encl llp df-void df-encl
    df-juxt df-encl df-juxt df-void df-encl df-encl llp df-juxt llp llp df-encl
    df-void df-encl df-encl df-juxt df-encl llp df-void df-encl df-juxt df-encl
    df-juxt df-void df-encl llp df-juxt df-encl llp df-juxt df-void df-encl
    df-encl llp df-juxt llp df-encl df-void df-encl df-encl df-juxt df-encl llp
    df-void df-encl df-juxt df-encl df-juxt llp df-void df-encl llp df-juxt
    df-encl df-juxt df-void df-encl llp df-juxt df-encl llp df-juxt llp df-encl
    df-void df-encl df-encl df-juxt df-encl llp df-void df-encl df-juxt df-encl
    df-juxt llp llp df-void df-encl df-juxt df-encl df-juxt llp df-void df-encl
    llp df-juxt df-encl df-juxt llp df-encl df-void df-encl df-encl df-juxt
    df-encl llp df-void df-encl df-juxt df-encl df-juxt llp df-encl df-encl llp
    df-void df-encl df-juxt df-encl df-juxt llp llp df-void df-encl df-juxt
    df-encl df-juxt df-void df-encl df-encl df-void llp df-encl df-void df-void
    llp df-void df-encl df-juxt df-encl i2 subb1 llp df-encl df-encl llp
    df-void llp df-void df-encl df-juxt df-encl llp c1 subst tran llp df-void
    df-encl df-void df-void df-void llp df-void cmmbx tran llp df-void df-encl
    llp df-juxt df-encl cmm tran df-void df-encl llp c2 tran df-void df-encl
    df-encl df-void df-void llp i2 subst tran $.

  $( Truth equivalence elimination.  $)
  ${
    elim.1 $e |- p = [ ] $.
    $( If p is equivalent to True, we can infer p .  (Contributed by Naip Moro,
       14-Feb-2017.) $)
    elim $p |- p $=
      llp df-encl df-void df-encl df-encl df-juxt df-encl llp df-void df-encl
      df-juxt df-encl df-juxt llp llp df-void df-encl elim.1 df-equ llp elimeq
      ax-qny $.
  $}

  $( Truth equivalence introduction.  $)
  ${
    intr.1 $e |- p $.
    $( If we can assert p, then we can infer that p is equivalent to True.
      (Contributed by Naip Moro, 14-Feb-2017.) $)
    intr $p |- p = [ ] $=
      llp df-void df-encl llp llp df-encl df-void df-encl df-encl df-juxt
      df-encl llp df-void df-encl df-juxt df-encl df-juxt intr.1 llp df-encl
      df-void df-encl df-encl df-juxt df-encl llp df-void df-encl df-juxt
      df-encl df-juxt llp llp elimeq sym ax-qny df-uni $.
  $}

  ${
    eucrelim.1 $e |- p = q $.
    eucrelim.2 $e |- p = [ ] $.
    $( Eliminate equation from 'eucr' deduction.  (Contributed by Naip Moro,
       14-Feb-2017.) $)
    eucrelim $p |- q $=
      llq llp llq df-void df-encl eucrelim.1 eucrelim.2 eucr elim $.
  $}

  ${
    tranelim.1 $e |- p = q $.
    tranelim.2 $e |- q = [ ] $.
    $( Eliminate equation from 'tran' deduction.  (Contributed by Naip Moro,
       14-Feb-2017.) $)
    tranelim $p |- p $=
      llp llp llq df-void df-encl tranelim.1 tranelim.2 tran elim $.
  $}

  ${
    and.1 $e |- p $.
    and.2 $e |- q $.
    $( Wrap premises in LoF conjunctive form.  From p and q we infer
       the LoF equivalent of p /\ q .  (Contributed by Naip Moro,
       14-Feb-2017.) $)
    and $p |- [ [ p ] [ q ] ] $=
      llp df-encl llq df-encl df-juxt df-encl llp df-encl llq df-encl df-juxt
      df-encl df-void df-encl llq df-juxt df-encl df-juxt llp df-encl llq
      df-encl df-juxt df-encl df-void df-encl df-void llq llp df-encl llq
      df-encl df-juxt df-encl df-void c3bx llp df-void df-encl df-void llq llp
      df-encl llq df-encl df-juxt df-encl df-void df-void df-encl llp and.1
      intr llp df-encl llq df-encl df-juxt df-encl llp llq df-juxt df-encl
      df-juxt llp llq llp df-void df-encl llq llp and.1 intr llq and.2 intr euc
      df-equ intr repbx eucr elim $.
  $}

  ${
    eq.1 $e |- p $.
    eq.2 $e |- q $.
    $( From assertions of p and q we infer their equality. (Contributed by Naip
       Moro, 1-Mar-2017.) $)
    eq $p |- p = q $=
      llp df-void df-encl llq llp eq.1 intr llq eq.2 intr euc $.
  $}

  ${
    mp.1 $e |- p $.
    mp.2 $e |- [ p ] q $.
    $( LoF version of modus ponens.  (Contributed by Naip Moro, 14-Feb-2017.) $)
    mp $p |- q $=
      llq llp df-encl df-void df-void llq df-void df-encl llp df-encl df-void
      df-encl df-encl df-void llp df-void df-encl llp mp.1 intr beq df-void c1
      tran llp df-encl llq df-juxt mp.2 intr rep elim $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   12. Defining classical propositional logic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  We define ( p -> q ) as [ p ] q and -. p as [ p ] , consistent with our
  interpretation of [ ] as True and the void as False, and determining the
  interpretation of the other logical constants:

  <HTML><br></HTML>

  <HTML><ul>
  <li> -. p = [ p ] .</li>
  <li> ( p -> q ) = [ p ] q .</li>
  <li> ( p \/ q ) = p q .</li>
  <li> ( p /\ q ) = [ [ p ] [ q ] ] .</li>
  <li> ( p <-> q ) = [ [ p ] [ q ] ] [ p q ] .</li>
  </ul></HTML>

  (NOTE:  LoF is "self-dual".  If we interpret [ ] as false and the void as
  true, the theorems of LoF remain valid but carry different meanings:

  <HTML><br></HTML>

  <HTML><ul>
  <li> -. p = [ p ] .</li>
  <li> ( p -> q ) = [ p [ q ] ] .</li>
  <li> ( p \/ q ) = [ [ p ] [ q ] ] .</li>
  <li> ( p /\ q ) = p q .</li>
  <li> ( p <-> q ) = [ [ [ p ] [ q ] ] [ p q ] ] .</li>
  </ul></HTML>

  This is C. S. Peirce's remarkable "alpha" system from his existential graphs,
  the first modern instance of a boundary algebra.)

  Constructing hybrid wffs like [ -. p ] that lack meaning in either LoF
  or propositional logic becomes not merely possible but necessary in the
  course of translating from one system to the other.  Indeed, one can validly
  calculate with these hybrid forms.  For example, [ -. p ] -. p can
  be reduced to [ ] by 'c2e' without the need to fully translate into LoF.  The
  proof of 'df-bimm' makes full use of that possibility.
$)

  $( Declare the primitive constant symbols for propositional calculus. $)
  $c ( $.  $( Left parenthesis $)
  $c ) $.  $( Right parenthesis $)
  $c -> $. $( Right arrow (read:  "implies") $)
  $c -. $. $( Right handle (read:  "not") $)

  $( Classical material implication is a wff. $)
  wi $a wff ( p -> q ) $.

  $( Classical negation is a wff. $)
  wn $a wff -. p $.

  $( Define material implication in terms of LoF. (Contributed by Naip Moro,
     27-Feb-2017.) $)
  df-imp $a |- ( p -> q ) = [ p ] q $.

  $( Define negation in terms of LoF. (Contributed by Naip Moro,
     27-Feb-2017.) $)
  df-neg $a |- -. p = [ p ] $.

  $( Express the negation of an implication.  (Contributed by Naip Moro,
     27-Feb-2017.) $)
  ni $p |- -. ( p -> q ) = [ [ p ] q ] $=
    llp llq wi llp df-encl llq df-juxt df-void df-void df-void df-void llp llq
    wi wn llp llq df-imp llp llq wi df-neg repbxs $.

  $( A hybrid theorem.  Enclosing the negation of a proposition is equivalent
     to the proposition.  (Contributed by Naip Moro, 28-Feb-2017.) $)
  ne $p |- [ -. p ] = p $=
    llp wn df-encl llp df-encl df-encl llp llp wn llp df-encl llp df-neg beq
    llp c1 tran $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                  13.  Propositional logic is superfluous
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Going forward, we can prove all the true statements of propositional logic
  (axioms and theorems) entirely in LoF and translate the results back into
  propositional form.  Below is an example where I prove Principia
  Mathematica's "proof by contradiction" theorem known as the Law of Clavius
  [WhiteheadRussell] p. 103.

  From the point of view of LoF, the Law of Clavius, like most theorems of
  propositional logic, is a trivial truth undeserving of the label "theorem".
  It would be as though someone claimed that "3x - 2x = x" was a "theorem" of
  numerical algebra.  Technically, yes ...

  It is not far-fetched to believe that one day LoF will supplant the
  propositional calculus, in the same way that brute algebraic computations
  (mostly) supplanted elegant geometric reasoning, and for much the same
  reasons.  But not in the manner shown here.  If you examine the proof below,
  you will appreciate the overhead involved in translating back and forth
  between the two systems.  Until predicate logic itself is replaced by a
  superior boundary formalism, and a single logic is deployed, one should not
  expect much movement on the part of logicians.
$)

  $( LoF version of set.mm's 'pm2.18'.  Law of Clavius.  (Contributed by Naip
     Moro, 14-Feb-2017.) $)
  clav $p |- ( ( -. p -> p ) -> p ) $=
    llp wn llp wi llp wi llp wn llp wi llp wi llp df-encl llp df-juxt df-void
    df-encl llp wn llp df-encl df-void llp llp wn llp wi llp wi llp df-neg llp
    wn llp wi llp wi llp wn df-encl llp df-juxt df-encl llp df-juxt llp wn llp
    df-juxt llp wn llp wi llp wn df-encl llp df-juxt df-void df-void df-void
    llp llp wn llp wi llp wi llp wn llp df-imp llp wn llp wi llp df-imp repbxs
    llp wn df-encl llp df-juxt df-encl llp df-juxt llp wn df-encl df-encl llp
    df-juxt llp wn llp df-juxt llp wn df-encl llp df-void df-void df-void
    df-void c2x llp wn df-void llp c1x tran tran reps llp df-void df-void
    df-void c2e tran elim $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
               14.  Proving the axioms of propositional logic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  In this section we prove the three axioms of set.mm's propositional calculus,
  as well as modus ponens.  This completes the task of demonstrating LoF's
  ability to ground the formalization of mathematics.
$)

  $( Proving set.mm's axiom 'ax-1' as a theorem.  (Contributed by Naip Moro,
     14-Feb-2017.) $)
  ax-1 $p |- ( p -> ( q -> p ) ) $=
    llp llq llp wi wi llp llq llp wi wi llp df-encl llq df-encl df-juxt llp
    df-juxt df-void df-encl llp llq llp wi wi llp df-encl llq llp wi df-juxt
    llp df-encl llq df-encl df-juxt llp df-juxt llp llq llp wi df-imp llq llp
    wi llq df-encl llp df-juxt llp df-encl llq llp df-imp subr tran llp
    df-void llq df-encl df-void c2e tran elim $.

  $( Proving set.mm's axiom 'ax-2' as a theorem.  (Contributed by Naip Moro,
     14-Feb-2017.) $)
  ax-2 $p |- ( ( p -> ( q -> r ) ) -> ( ( p -> q ) -> ( p -> r ) ) ) $=
    llp llq llr wi wi llp llq wi llp llr wi wi wi llp llq llr wi wi llp llq wi
    llp llr wi wi wi llp df-encl llq df-encl df-juxt llr df-juxt df-encl llp
    df-encl df-juxt llq df-encl df-juxt llr df-juxt df-void df-encl llp llq llr
    wi wi llp llq wi llp llr wi wi wi llp df-encl llq df-encl df-juxt llr
    df-juxt df-encl llq df-encl df-juxt llp df-encl df-juxt llr df-juxt llp
    df-encl llq df-encl df-juxt llr df-juxt df-encl llp df-encl df-juxt llq
    df-encl df-juxt llr df-juxt llp llq llr wi wi llp llq wi llp llr wi wi wi
    llp df-encl llq df-encl df-juxt llr df-juxt df-encl llp df-encl llq df-juxt
    df-encl df-juxt llp df-encl df-juxt llr df-juxt llp df-encl llq df-encl
    df-juxt llr df-juxt df-encl llq df-encl df-juxt llp df-encl df-juxt llr
    df-juxt llq llr wi llq df-encl llr df-juxt llp df-encl df-void df-void llp
    df-encl llq df-juxt df-encl llp df-encl df-juxt llr df-juxt llp llq llr wi
    wi llp llq wi llp llr wi wi wi llq llr df-imp llp llq llr wi wi llp df-encl
    llq llr wi df-juxt df-void df-void df-void llp df-encl llq df-juxt df-encl
    llp df-encl df-juxt llr df-juxt llp llq llr wi wi llp llq wi llp llr wi wi
    wi llp llq llr wi df-imp llp llq wi llp df-encl llq df-juxt df-void df-void
    llp llq llr wi wi df-encl llp df-encl llr df-juxt llp llq llr wi wi llp llq
    wi llp llr wi wi wi llp llq df-imp llp llr wi llp df-encl llr df-juxt llp
    llq llr wi wi df-encl llp llq wi df-encl df-juxt df-void llp llq llr wi wi
    llp llq wi llp llr wi wi wi llp llr df-imp llp llq wi llp llr wi wi llp llq
    wi df-encl llp llr wi df-juxt llp llq llr wi wi df-encl df-void llp llq llr
    wi wi llp llq wi llp llr wi wi wi llp llq wi llp llr wi df-imp llp llq llr
    wi wi llp llq wi llp llr wi wi df-imp reps reps repbxs repbxs repbxs
    df-void llp df-encl llp df-encl llq df-encl df-juxt llr df-juxt df-encl llq
    df-void llr c2x tran llq df-encl llp df-encl llp df-encl llq df-encl
    df-juxt llr df-juxt df-encl df-void llr cmmx tran llp df-encl llq df-encl
    df-juxt llr df-juxt df-void df-void df-void c2e tran elim $.

  $( Proving set.mm's axiom 'ax-3' as a theorem.  (Contributed by Naip Moro,
     14-Feb-2017.) $)
  ax-3 $p |- ( ( -. p -> -. q ) -> ( q -> p ) ) $=
    llp wn llq wn wi llq llp wi wi llp wn llq wn wi llq llp wi wi llp df-encl
    llq df-encl df-juxt llp df-juxt df-void df-encl llp wn llq wn wi llq llp wi
    wi llp df-encl df-encl df-encl llq df-encl df-juxt llp df-juxt llp df-encl
    llq df-encl df-juxt llp df-juxt llp wn llq wn wi llq llp wi wi llp df-encl
    df-encl llq df-encl df-juxt df-encl llq df-encl df-juxt llp df-juxt llp
    df-encl df-encl df-encl llq df-encl df-juxt llp df-juxt llq wn llq df-encl
    llp df-encl df-encl df-void df-void llq df-encl llp df-juxt llp wn llq wn
    wi llq llp wi wi llq df-neg llp wn df-encl llp df-encl df-encl df-void llq
    wn df-void llq df-encl llp df-juxt llp wn llq wn wi llq llp wi wi llp wn
    llp df-encl llp df-neg beq llp wn llq wn wi llp wn df-encl llq wn df-juxt
    df-void df-void df-void llq df-encl llp df-juxt llp wn llq wn wi llq llp wi
    wi llp wn llq wn df-imp llq llp wi llq df-encl llp df-juxt llp wn llq wn wi
    df-encl df-void llp wn llq wn wi llq llp wi wi llq llp df-imp llp wn llq wn
    wi llq llp wi df-imp reps repbxs repbxs repbxs llp df-encl df-encl llq
    df-encl df-void df-void df-void llp c2x tran llp df-void df-void df-void
    llq df-encl llp df-juxt c1bx tran llp df-void llq df-encl df-void c2e
    tran elim $.

  ${
    $( Minor premise for modus ponens. $)
    min $e |- p $.
    $( Major premise for modus ponens. $)
    maj $e |- ( p -> q ) $.
    $( Proving set.mm's modus ponens 'ax-mp' as a theorem.  (Contributed by
       Naip Moro, 14-Feb-2017.) $)
    ax-mp $p |- q $=
      llp llq min llp df-encl llq df-juxt llp llq wi llp df-encl llq df-juxt
      df-void df-encl llp llq df-imp llp llq wi maj intr eucr elim mp $.
  $}

  $( With the proofs of 'ax-1', 'ax-2', 'ax-3', and 'ax-mp' completed, we can
     retire LoF and proceed with the classical development of metamath's logic.
     But first, a foray into the theory of the biconditional. $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                            15.  The biconditional
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  set.mm's section on the biconditional begins with the definition of 'df-bi' :
  -. ( ( ( p <-> q ) -> -. ( ( p -> q ) -> -. ( q -> p ) ) )
    -> -. ( -. ( ( p -> q ) -> -. ( q -> p ) ) -> ( p <-> q ) ) )
  followed by three theorems that depend on it:  'bi1mm', 'bi3', and 'dfbi1'.
  Here we utilize the equivalence of the biconditional with equality to prove
  all four of those statements, including the definition, directly from LoF.

  In examining this section, the reader may wonder about the need for the
  equality sign, and in fact we could have dispensed with it, replacing "="
  with "<->" right from the start.  I retained it for readability and to avoid
  some nuanced distinctions.  For example, while ( p <-> q ) is a wff, p = q
  cannot be one without introducing contradiction (see Appendix A for details).
$)

  $( Declare the biconditional symbol. $)
  $c <-> $.

  $( The biconditional is a wff. $)
  wb $a wff ( p <-> q ) $.

  $( A definition of the biconditional in terms of LoF equality.  (Contributed
     by Naip Moro, 21-Feb-2017.) $)
  df-bic $a |- ( p <-> q ) = [ [ p ] [ q ] ] [ p q ] $.

  $( A more traditional understanding of the biconditional as (the LoF
     equivalent of) a conjunction of converse implications.  (Contributed by
     Naip Moro, 24-Feb-2017.) $)
  bici $p |- ( p <-> q ) = [ [ [ p ] q ] [ [ q ] p ] ] $=
    llp llq wb llp df-encl llq df-encl df-juxt df-encl llp llq df-juxt df-encl
    df-juxt llp df-encl llq df-juxt df-encl llq df-encl llp df-juxt df-encl
    df-juxt df-encl llp llq df-bic llp llq biimp euc $.

  $( This is similar, in fact equivalent, to set.mm's 'dfbi1'. (Contributed by
     Naip Moro, 25-Feb-2017.) $)
  bic1 $p |- ( p <-> q ) = -. ( ( p -> q ) -> -. ( q -> p ) ) $=
    llp llq wb llp df-encl llq df-juxt df-encl llq df-encl llp df-juxt df-encl
    df-juxt df-encl llp llq wi llq llp wi wn wi wn llp llq bici llp llq wi
    llq llp wi wn wi wn llp df-encl llq df-juxt df-encl llq llp wi df-encl
    df-juxt df-encl llp df-encl llq df-juxt df-encl llq df-encl llp df-juxt
    df-encl df-juxt df-encl llp llq wi llq llp wi wn wi wn llp llq wi df-encl
    llq llp wi df-encl df-juxt df-encl llp df-encl llq df-juxt df-encl llq llp wi
    df-encl df-juxt df-encl llp llq wi llq llp wi wn wi wn llp llq wi df-encl
    llq llp wi wn df-juxt df-encl llp llq wi df-encl llq llp wi df-encl df-juxt
    df-encl llp llq wi llq llp wi wn wi wn llp llq wi llq llp wi wn wi df-encl
    llp llq wi df-encl llq llp wi wn df-juxt df-encl llp llq wi llq llp wi wn
    wi df-neg llp llq wi llq llp wi wn wi llp llq wi df-encl llq llp wi wn
    df-juxt df-void df-void df-void df-void llp llq wi llq llp wi wn df-imp
    subb1 tran llq llp wi wn llq llp wi df-encl llp llq wi df-encl df-void
    df-void df-void llq llp wi df-neg subb1 tran llp llq wi llp df-encl llq
    df-juxt df-void df-void df-void llq llp wi df-encl df-void df-void llp llq
    df-imp subbd1 tran llq llp wi llq df-encl llp df-juxt df-void df-void llp
    df-encl llq df-juxt df-encl df-void df-void df-void llq llp df-imp subbd1
    tran euc $.

  $( The reverse of 'bic1'.  (Contributed by Naip Moro, 26-Feb-2017.) $)
  bic1r $p |- -. ( ( p -> q ) -> -. ( q -> p ) ) = ( p <-> q ) $=
    llp llq wb llp llq wi llq llp wi wn wi wn llp llq bic1 sym $.

  $( This is set.mm's biconditional definition 'df-bi' proved as a theorem.
     (Contributed by Naip Moro, 28-Feb-2017.) $)
  dfbic $p |- -. ( ( ( p <-> q ) -> -. ( ( p -> q ) -> -. ( q -> p ) ) )
              -> -. ( -. ( ( p -> q ) -> -. ( q -> p ) ) -> ( p <-> q ) ) ) $=
    llp llq wb llp llq wi llq llp wi wn wi wn wi llp llq wi llq llp wi wn wi wn
    llp llq wb wi wn wi wn llp llq wb llp llq wi llq llp wi wn wi wn wi llp llq
    wi llq llp wi wn wi wn llp llq wb wi wn wi wn llp llq wb df-encl llp llq wb
    df-juxt df-void df-encl llp llq wi llq llp wi wn wi wn llp llq wb df-void
    df-void df-void llp llq wb llp llq wb llp llq wi llq llp wi wn wi wn wi llp
    llq wi llq llp wi wn wi wn llp llq wb wi wn wi wn llp llq bic1r llp llq wb
    llp llq wi llq llp wi wn wi wn wi llp llq wi llq llp wi wn wi wn llp llq wb
    wi wn wi wn llp llq wi llq llp wi wn wi wn llp llq wb wi llp llq wi llq llp
    wi wn wi wn df-encl llp llq wb df-juxt llp llq wb llp llq wi llq llp wi wn
    wi wn wi llp llq wi llq llp wi wn wi wn llp llq wb wi wn wi wn llp llq wi
    llq llp wi wn wi wn llp llq wb wi wn df-encl llp llq wi llq llp wi wn wi wn
    llp llq wb wi llp llq wb df-encl llp llq wb df-juxt df-encl df-void df-void
    llp llq wi llq llp wi wn wi wn llp llq wb wi wn df-void df-void llp llq wb
    llp llq wi llq llp wi wn wi wn wi llp llq wi llq llp wi wn wi wn llp llq wb
    wi wn wi wn llp llq wb ax-j1 llp llq wi llq llp wi wn wi wn llp llq wb llp
    llq wb df-encl df-void df-void llp llq wi llq llp wi wn wi wn llp llq wb wi
    wn df-void df-void llp llq wb llp llq wi llq llp wi wn wi wn wi llp llq wi
    llq llp wi wn wi wn llp llq wb wi wn wi wn llp llq bic1r llp llq wb llp llq
    wi llq llp wi wn wi wn wi llp llq wb df-encl llp llq wi llq llp wi wn wi wn
    df-juxt df-void df-void df-void llp llq wi llq llp wi wn wi wn llp llq wb
    wi wn df-void df-void llp llq wb llp llq wi llq llp wi wn wi wn wi llp llq
    wi llq llp wi wn wi wn llp llq wb wi wn wi wn llp llq wb llp llq wi llq llp
    wi wn wi wn df-imp llp llq wb llp llq wi llq llp wi wn wi wn wi llp llq wi
    llq llp wi wn wi wn llp llq wb wi wn ni repbdxs repbdxs repbxs llp llq wi
    llq llp wi wn wi wn llp llq wb wi ne tran llp llq wi llq llp wi wn wi wn
    llp llq wb df-imp tran repbxs llp llq wb df-void df-void df-void c2e tran
    elim $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                         16.  Equality as a wff
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A parenthesized equality is a wff. $)
  wfe $a wff ( p = q ) $.

  $( The definition of parenthesized equality is, of course, the same as the
     joint definitions of equality 'df-equ' and 'df-uni', except that the
     latter need to be in the form of inferences.  (Contributed by Naip Moro,
     14-Oct-2017.) $)
  df-pareq $a |- ( p = q ) = [ [ p ] [ q ] ] [ p q ] $.

  $( Parentheses can be removed from an equality.  (Contributed by Naip Moro,
     14-Oct-2017.) $)
  ${
    parrm.1 $e |- ( p = q ) $.
    parrm $p |- p = q  $=
      llp llq llp df-encl llq df-encl df-juxt df-encl llp llq df-juxt df-encl
      df-juxt llp llq wfe llp df-encl llq df-encl df-juxt df-encl llp llq
      df-juxt df-encl df-juxt df-void df-encl llp llq df-pareq llp llq wfe
      parrm.1 intr eucr elim df-uni $.
  $}

  $( Parentheses can be added to an equality.  (Contributed by Naip Moro,
     14-Oct-2017.) $)
  ${
    parad.1 $e |- p = q $.
    parad $p |- ( p = q ) $=
      llp llq wfe llp llq wfe llp df-encl llq df-encl df-juxt df-encl llp
      llq df-juxt df-encl df-juxt df-void df-encl llp llq df-pareq llp df-encl
      llq df-encl df-juxt df-encl llp llq df-juxt df-encl df-juxt llp llq
      parad.1 df-equ intr tran elim $.
  $}

  $( Demonstrating again that equality equals the biconditional.  (Contributed
     by Naip Moro, 14-Oct-2017.) $)
  eqeqbi $p |- ( p = q ) = ( p <-> q ) $=
    llp llq wfe llp df-encl llq df-encl df-juxt df-encl llp llq df-juxt
    df-encl df-juxt llp llq wb llp llq df-pareq llp llq df-bic euc $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                           17.  Equational logic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)



$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                                18.  Conclusion
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  To show that this file can replace set.mm's classical logic, remove (or
  comment out) the following sections of set.mm:
    *  Pre-logic.
    *  Recursively define primitive wffs for propositional calculus.
    *  The axioms of propositional calculus.

  and remove (or comment out) the following statements:
    *  the declaration of the constants: "[", "]", "=", and "<->".
    *  wb , df-bimm , bi1mm , bi3 , dfbi1 .

  Now either:  1) Paste the contents of this file anywhere before the start of
  set.mm's active statements, or 2) Add "$[ lofset.mm $]" to the beginning of
  set.mm (making sure lofset.mm is in the same directory as set.mm).  Read the
  ensuing (saved) file into metamath and run the command "verify proof *".
  Expected result:  "All proofs in the database were verified".

  An example of such an altered set.mm file (via option 1) is available here:
  https://github.com/naipmoro/lofmm/blob/master/set(lof).mm .

  This file has been tested with the master branch of set.mm (commit
  558ed611a8d20ccdf7d486f19ad86c76bbab59e0 on 20-Dec-2016) available at
  https://github.com/metamath/set.mm/blob/master/set.mm , and with the
  develop branch (commit ceddb016b6450c6ee9f6f811196345a4e9395838 on
  1-Mar-2017) at https://github.com/metamath/set.mm/blob/develop/set.mm .
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                                 Appendix A
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Another important difference between LoF and equational logic: the latter
  allows forms such as p = p = [ ] and [ p ] = p = by ascribing
  well-formedness to binary equations, while in LoF this would result in
  contradiction, as demonstrated by the following (commented out) derivation.

  @( Assume an equation is a wff. @)
  eqwff $a wff p = q $.

  @( Outline of the proof of nono:

     <HTML><br></HTML>

     <HTML><ol>
     <li> p = p           (id)        </li>
     <li> p = p = [ ]     (1 intr)    </li>
     <li> p = p q = [ ] q (2 sub)     </li>
     <li> [ ] q = [ ]     (c3)        </li>
     <li> p = p q = [ ]   (3,4 trans) </li>
     <li> p = p q         (5 elim)    </li>
     </ol></HTML>
     (Contributed by Naip Moro, 11-Mar-2017.) @)
  nono $p |- p = p q $=
    ( eqwff df-juxt df-void df-encl intr sub tran elim id c3 ) AACZBDZNEFZBDOM
    OBMAKGHBLIJ $.

  @( Derive a contradiction:  We prove false is equal to true by substituting
     the appropriate values into nono .  (Contributed by Naip Moro,
     11-Mar-2017.) @)
  contradiction $p |-  = [ ] $=
    ( df-void df-encl nono ) AABC $.
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                                 REFERENCES
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  1. [Schroeder2] Schroeder, Ernst, "Vorlesungen ueber die Algebra der Logik
     (exakte Logik)", vol. II, part 1, Teubner, Leipzig (1891).
  2. [Spencer-Brown] Spencer-Brown, George, "Laws of Form", Allen & Unwin,
     London (1969).
$)

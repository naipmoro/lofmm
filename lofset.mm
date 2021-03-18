$( lofset.mm - Version of 17-March-2021 $)

$(
  Version 0.3.0
  Copyright (C) 2015-2021 Naip Moro

  This file is made available under the MIT License:
  http://opensource.org/licenses/MIT

  This file contains verbatim excerpts from set.mm
  (found at ~ https://github.com/metamath/set.mm/blob/master/set.mm ) which
  is released under the CC0 1.0 Universal public domain license.
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                              0. Introduction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  In lof.mm ( ~ https://github.com/naipmoro/lofmm/blob/master/lof.mm ) I
  presented metamath derivations of Spencer-Brown's Primary Algebra (details of
  the algebra, hereafter cited as "LoF", can be found in Chapter 6 of
  [Spencer-Brown]).  lof.mm was a stand-alone project incompatible with set.mm,
  metamath's ongoing formalization of mathematics.  In contrast, here I present
  a version which is strictly compatible:  I derive set.mm's propositional
  calculus from LoF.  There is nothing surprising in this -- classical
  propositional logic is one of the interpretations of LoF (Boolean algebra is
  another).  The real interest lies in the means of derivation. 

  LoF is an equational logic (although I show that, technically, equations can
  be avoided).  In other words, axioms and theorems are stated in the form
  ` ph = ps ` .  Transitioning from this to the implicational form
  characteristic of classical logic is an interesting problem.  I believe the
  technique chosen here is among the simplest, relying on a single additional
  axiom ~ ax-lofqny (known as Equanimity), the equational analogue of modus
  ponens:

  ${
    ax-lofqny.1 $e |- ph $.
    ax-lofqny.2 $e |- ph = ps $.
    ax-lofqny   $a |- ps $.
  $}

  With this rule in hand, and with appropriate definitions of "implies" and
  "not", I prove the axioms of set.mm, ~ ax-1 , ~ ax-2 , ~ ax-3 , and ~ ax-mp ,
  as theorems of LoF.

  (Note about notation:  All LoF theorems have labels prefixed with "lof",
  while axioms and definitions are prefixed with "ax-lof" and "df-lof",
  respectively.  Statements from set.mm retain their original labels.)
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                            1. The alphabet of LoF
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare the primitive constant symbols. $)
  $c [ $. $( Left side of boundary $)
  $c ] $. $( Right side of boundary $)
  $c wff $. $( Well-formed formula symbol (read:  "the following symbol
               sequence is a wff") $)
  $c |- $. $( Turnstile (read:  "the following symbol sequence is provable" or
              'a proof exists for") $)

  $( Introduce variables to represent the well-formed formulas. $)
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

  $( Specify some variables that we will use to represent wff's. $)
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
  df-lofvoid $a wff $.

  $( If ` ph ` is a wff, so is ` [ ph ] ` .  We say that " ` ph ` is enclosed
     (or crossed, or marked)".  Combined with the previous definition, we see
     that ` [ ] ` , ` [ [ ] ] ` , ` [ ... [ [ ] ] ... ] ` are all wffs.
     Spencer-Brown calls ` [ ] ` the "marked state" and we identify it with the
     value True.  (Contributed by Naip Moro, 2-Sep-2015.) $)
  df-lofencl $a wff [ ph ] $.

  $( If ` ph ` and ` ps ` are wffs, so is ` ph ps ` .  We say that " ` ph ` is
     juxtaposed with ` ps ` ."  As with the Dyck language, this rule introduces
     a technical ambiguity into the grammar and some parsers will reject it.
     However, since juxtaposition is inherently associative, this ambiguity
     does not compromise the validity of the ensuing derivations and all proper
     proof verifiers will accept them.  (Contributed by Naip Moro,
     2-Sep-2015.) $)
  df-lofjuxt $a wff ph ps $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                  3. The four primitive inference axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  In lof.mm "=" was one of the primitive constants of the language.  But the
  symbol is superfluous, as in a Boolean system equality and equivalence are
  synonyms.  Let us interpret the form ` [ [ ph ] [ ps ] ] [ ph ps ] ` to mean
  " ` ph ` equals (or is equivalent to) ` ps ` ".  All of LoF can be expressed
  accordingly, and I will call this the "unitary form" of LoF.  For
  demonstration purposes, I state the four primitive inference rules of LoF and
  a handful of associated theorems in this form.  But what is theoretically
  possible is not always cognitively palatable, and I subsequently abandon this
  approach and return to explicit equations, what I call LoF's "equational
  form".
$)

  ${
    ax-lofeuc.1 $e |- [ [ ph ] [ ps ] ] [ ph ps ] $.
    ax-lofeuc.2 $e |- [ [ ch ] [ ps ] ] [ ch ps ] $.
    $( Read this as:  "If ` ph ` is equal to ` ps ` and ` ch ` is equal to
       ` ps ` , then we can infer that ` ph ` is equal to ` ch ` ".  In other
       words, two things equal to the same thing are equal to each other.  This
       is Euclid's first Common Notion and, in an equational logic, this and
       its sibling, transitivity, are the main engine of derivation.
       (Contributed by Naip Moro, 26-Jan-2017.) $)
    ax-lofeuc $a |- [ [ ph ] [ ch ] ] [ ph ch ] $.
  $}

  $( We can rephrase Euclid's second and third Common Notions as:  Doing the
     same thing (e.g., applying the same operation) to equal things leaves
     equal things.  In light of LoF's two operations, enclosure and
     juxtaposition, this leads to the next two axioms (looked at differently,
     these can also be seen as substitution/replacement rules). $)

  ${
    ax-lofbeq.1 $e |- [ [ ph ] [ ps ] ] [ ph ps ] $.
    $( Read this as:  "If ` ph ` is equal to ` ps ` , then we can infer that
       ` [ ph ] ` is equal to ` [ ps ] ` ".  Enclosing equal forms leaves equal
       forms.  (Contributed by Naip Moro, 26-Jan-2017.) $)
    ax-lofbeq $a |- [ [ [ ph ] ] [ [ ps ] ] ] [ [ ph ] [ ps ] ]
    $.
  $}

  ${
    ax-lofsub.1 $e |- [ [ ph ] [ ps ] ] [ ph ps ] $.
    $( Read this as:  "If ` ph ` is equal to ` ps ` , then we can infer that
       ` ph ch ` is equal to ` ps ch ` for any ` ch ` ".  Juxtaposing the same
       form with equal forms leaves equal forms.  (Contributed by Naip Moro,
       26-Jan-2017.) $)
    ax-lofsub $a |- [ [ ph ch ] [ ps ch ] ] [ ph ch ps ch ] $.
  $}

  $( Commutativity of LoF.  $)

  $( Read this as:  " ` ph ps ` is equal to ` ps ph ` ".  Of the four axioms,
     only this one is domain-specific.  (Contributed by Naip Moro,
     26-Jan-2017.) $)
  ax-lofcmm $a |- [ [ ph ps ] [ ps ph ] ] [ ph ps ps ph ] $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                    4. Equality is an equivalence relation
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  If our target interpretation is to be satisfied, we should expect "equality"
  to meet the requirements of an equivalence relation: reflexivity, symmetry,
  and transitivity.  The next three theorems show that it does.
$)

  $( "Equality" is reflexive.  Read this as:  " ` ph ` is equal to ` ph ` ".
     (Contributed by Naip Moro, 26-Jan-2017.) $)
  lofidu $p |- [ [ ph ] [ ph ] ] [ ph ph ] $=
    ( df-lofvoid ax-lofcmm ) ABC $.

  ${
    lofsymu.1 $e |- [ [ ph ] [ ps ] ] [ ph ps ] $.
    $( "Equality" is symmetric.  Read this as:  "If ` ph ` is equal to ` ps ` ,
       then we can infer that ` ps ` is equal to ` ph ` ".  (Contributed by
       Naip Moro, 26-Jan-2017.) $)
    lofsymu $p |- [ [ ps ] [ ph ] ] [ ps ph ] $=
      ( lofidu ax-lofeuc ) BBABDCE $.
  $}

  ${
    loftransu.1 $e |- [ [ ph ] [ ps ] ] [ ph ps ] $.
    loftransu.2 $e |- [ [ ps ] [ ch ] ] [ ps ch ] $.
    $( "Equality" is transitive.  Read this as:  "If ` ph ` is equal to ` ps `
       and ` ps ` is equal to ` ch ` , then we can infer that ` ph ` is equal
       to ` ch ` ".  (Contributed by Naip Moro, 26-Jan-2017.) $)
    loftransu $p |- [ [ ph ] [ ch ] ] [ ph ch ] $=
      ( lofsymu ax-lofeuc ) ABCDBCEFG $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                     5. Introducing the equality symbol
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  We can go only so far with the unitary form before reasoning becomes
  intolerably cumbersome.  In introducing "=", note that it is a relation
  between wffs and _not itself part of a wff_.  Jointly, the two definitions
  that follow allow us to translate back and forth between LoF's unitary and
  equational forms.
$)

  $c = $. $( Equality (read:  "is equal to" or "is equivalent to") $)

  ${
    df-lofequ.1 $e |- ph = ps $.
    $( Define equality in terms of LoF's unitary formalism.  (Contributed by
       Naip Moro, 26-Jan-2017.) $)
    df-lofequ $a |- [ [ ph ] [ ps ] ] [ ph ps ] $.
  $}

  ${
    df-lofuni.1 $e |- [ [ ph ] [ ps ] ] [ ph ps ] $.
    $( Translate LoF's unitary form into equational form.  (Contributed by Naip
       Moro, 26-Jan-2017.) $)
    df-lofuni $a |- ph = ps $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                       6. Equality-based theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Traditional equational logic is based on four inference rules
  (see ~ https://en.wikipedia.org/wiki/Equational_logic ):

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

  How does this compare with LoF? For one thing, Substitution is not needed,
  as it is pre-built into metamath.  While the generality of the Leibniz rule
  is not available to us, any particular instance of it is conceptually
  captured by the two rules ~ lofbeq and ~ lofsub .  Transitivity is replaced
  by Euclid's equivalent rule ~ lofeuc (we prove Transitivity as a theorem).
  Finally, Equanimity is not needed until we begin to interface with classical
  propositional logic (and even then there might be a simpler approach).  This
  suggests that LoF is more accurately characterized as a proto-equational
  logic.  LoF's formal system does require commutativity, clearly an extraneous
  addition; but bear in mind that LoF is intrinsically a planar notation, where
  commutativity is an unstated given. It is only in the context of a linear
  notation like metamath that an explicit reference to commutativity is
  required.
$)

  ${
    lofeuc.1 $e |- ph = ps $.
    lofeuc.2 $e |- ch = ps $.
    $( The equational-form version of ~ ax-lofeuc .  (Contributed by Naip Moro,
       26-Jan-2017.) $)
    lofeuc $p |- ph = ch $=
      ( df-lofequ ax-lofeuc df-lofuni ) ACABCABDFCBEFGH $.
  $}

  ${
    lofbeq.1 $e  |- ph = ps $.
    $( The equational-form version of ~ ax-lofbeq .  (Contributed by Naip Moro,
       26-Jan-2017.) $)
    lofbeq $p |- [ ph ] = [ ps ] $=
      ( df-lofencl df-lofequ ax-lofbeq df-lofuni ) ADBDABABCEFG $.
  $}

  ${
    lofsub.1 $e |- ph = ps $.
    $( The equational-form version of ~ ax-lofsub .  (Contributed by Naip Moro,
       26-Jan-2017.) $)
    lofsub $p |- ph ze = ps ze $=
      ( df-lofjuxt df-lofequ ax-lofsub df-lofuni ) ACEBCEABCABDFGH $.
  $}

  $( The equational-form version of ~ ax-lofcmm .  (Contributed by Naip Moro,
     26-Jan-2017.) $)
  lofcmm $p |- ph ps = ps ph $=
    ( df-lofjuxt ax-lofcmm df-lofuni ) ABCBACABDE $.

  $( The equational-form version of ~ lofidu .  (Contributed by Naip Moro,
     6-Sep-2015.) $)
  lofid $p |- ph = ph $=
    ( df-lofvoid lofcmm ) ABC $.

  ${
    lofsym.1 $e |- ph = ps $.
    $( The equational-form version of ~ lofsymu .  (Contributed by Naip Moro,
       2-Sep-2015.) $)
    lofsym $p |- ps = ph $=
      ( lofid lofeuc ) BBABDCE $.
  $}

  ${
    loftrans.1 $e |- ph = ps $.
    loftrans.2 $e |- ps = ch $.
    $( The equational-form version of ~ loftransu .  (Contributed by Naip Moro,
       2-Sep-2015.) $)
    loftrans $p |- ph = ch $=
      ( lofsym lofeuc ) ABCDBCEFG $.
  $}

  ${
    lofeucr.1 $e |- ph = ps $.
    lofeucr.2 $e |- ph = ch $.
    $( A commuted - or reversed - version of ~ lofeuc .  (Contributed by Naip
       Moro, 2-Sep-2015.) $)
    lofeucr $p |- ps = ch $=
      ( lofsym loftrans ) BACABDFEG $.
  $}

  ${
    lofsubr.1 $e |- ph = ps $.
    $( A commuted version of ~ lofsub .  (Contributed by Naip Moro,
       2-Sep-2015.) $)
    lofsubr $p |- et ph = et ps $=
      ( df-lofjuxt lofsub lofcmm lofeucr ) BCEZCAEZCBEACEIJABCDFACGHBCGH $.
  $}

  $( More versions of replacement/substitution. $)
  ${
    lofsubst.1 $e |- ph = ps $.
    $( Replace a form with an equal form within an extended form.  (Contributed
       by Naip Moro, 2-Sep-2015.) $)
    lofsubst $p |- et ph ze = et ps ze $=
      ( df-lofjuxt lofsub lofsubr ) ADFBDFCABDEGH $.

    $( Replace a form with an equal form within a commuted extended form.
       (Contributed by Naip Moro, 2-Sep-2015.) $)
    lofsubstr $p |- et ph ze = ze ps et $=
      ( df-lofjuxt lofsub lofcmm loftrans lofsubr ) CAFDFCDFBFDBFZCFADFZKCLBDFK
      ABDEGBDHIJCKHI $.

    $( Replace a form with an equal form within a bounded extended form.
       (Contributed by Naip Moro, 2-Sep-2015.) $)
    lofsubb1 $p |- si [ et ph ze ] rh = si [ et ps ze ] rh $=
      ( df-lofjuxt df-lofencl lofsubst lofbeq ) CAHDHZICBHDHZIEFLMABCDGJKJ $.

    $( Replace a form with an equal form within a double-bounded extended
       form.  (Contributed by Naip Moro, 25-Feb-2017.) $)
    lofsubbd1 $p |- mu [ si [ et ph ze ] rh ] la
                    = mu [ si [ et ps ze ] rh ] la $=
      ( df-lofjuxt df-lofencl df-lofvoid lofsubb1 ) ECAJDJKJFJECBJDJKJFJLLGHABC
      DEFIMM $.

    $( Replace a form with an equal form within a bounded and commuted extended
       form.  (Contributed by Naip Moro, 2-Sep-2015.) $)
    lofsubb2 $p |- si [ et ph ze ] rh = si [ ze ps et ] rh $=
      ( df-lofjuxt df-lofencl lofsubstr lofbeq lofsubst ) CAHDHZIDBHCHZIEFMNABC
      DGJKL $.
  $}

  ${
    lofrep.1 $e |- ph = ps $.
    lofrep.2 $e |- et ph ze = mu $.
    $( Direct substitution into lhs of an equation.  (Contributed by Naip Moro,
       18-Sep-2015.) $)
    lofrep $p |- et ps ze = mu $=
      ( df-lofjuxt lofsubst lofeucr ) CAHDHCBHDHEABCDFIGJ $.
  $}

  ${
    lofreps.1 $e |- ph = ps $.
    lofreps.2 $e |- mu = et ph ze $.
    $( Direct substitution into rhs of an equation.  (Contributed by Naip Moro,
       14-Feb-2017.) $)
    lofreps $p |- mu = et ps ze $=
      ( df-lofjuxt lofsym lofrep ) CBHDHEABCDEFECAHDHGIJI $.
  $}

  ${
    lofrepbx.1 $e |- ph = ps $.
    lofrepbx.2 $e |- si [ et ph ze ] rh = mu $.
    $( Direct substitution into lhs of a bounded-form equation.  (Contributed
       by Naip Moro, 18-Sep-2015.) $)
    lofrepbx $p |- si [ et ps ze ] rh = mu $=
      ( df-lofjuxt df-lofencl lofsubb1 lofeucr ) ECAJDJKJFJECBJDJKJFJGABCDEFHLI
      M $.
  $}

  ${
    lofrepbdx.1 $e |- ph = ps $.
    lofrepbdx.2 $e |- mu [ si [ et ph ze ] rh ] la = ka $.
    $( Direct substitution into lhs of a double-bounded equation.  (Contributed
       by Naip Moro, 27-Feb-2017.) $)
    lofrepbdx $p |- mu [ si [ et ps ze ] rh ] la = ka $=
      ( df-lofjuxt df-lofencl lofsubbd1 lofeucr ) GECALDLMLFLMLHLGECBLDLMLFLMLH
      LIABCDEFGHJNKO $.
  $}

  ${
    lofrepbxs.1 $e |- ph = ps $.
    lofrepbxs.2 $e |- mu = si [ et ph ze ] rh $.
    $( Direct substitution into rhs of a bounded equation.  (Contributed by
       Naip Moro, 14-Feb-2017.) $)
    lofrepbxs $p |- mu = si [ et ps ze ] rh $=
      ( df-lofjuxt df-lofencl lofsym lofrepbx ) ECBJDJKJFJGABCDEFGHGECAJDJKJFJI
      LML $.
  $}

  ${
    lofrepbdxs.1 $e |- ph = ps $.
    lofrepbdxs.2 $e |- ka = mu [ si [ et ph ze ] rh ] la $.
    $( Direct substitution into rhs of a double-bounded equation.  (Contributed
       by Naip Moro, 27-Feb-2017.) $)
    lofrepbdxs $p |- ka = mu [ si [ et ps ze ] rh ] la $=
      ( df-lofjuxt df-lofencl lofsym lofrepbdx ) GECBLDLMLFLMLHLIABCDEFGHIJIGEC
      ALDLMLFLMLHLKNON $.
  $}

  ${
    lofrepbd.1 $e |- ph = ps $.
    lofrepbd.2 $e |- [ [ et ph ze ] ] = mu $.
    $( Direct substitution into lhs of a double-bounded equation.  (Contributed
       by Naip Moro, 3-Oct-2015.) $)
    lofrepbd $p |- [ [ et ps ze ] ] = mu $=
      ( df-lofjuxt df-lofencl df-lofvoid lofsubb1 lofbeq lofeucr ) CAHDHIZICBHD
      HIZIENOABCDJJFKLGM $.
  $}

  ${
    lofquad.1 $e |- ph = ps $.
    lofquad.2 $e |- ch = th $.
    $( Double substitution of equivalent forms.  (Contributed by Naip Moro,
       2-Sep-2015.) $)
    lofquad $p |- ph ch = ps th $=
      ( df-lofjuxt df-lofvoid lofsubst loftrans ) ACGBCGBDGABHCEICDBHFIJ $.
  $}

  ${
    lofins.1 $e |- ph ps = ch th $.
    $( Insert the same form into two equivalent forms.  (Contributed by Naip
       Moro, 3-Sep-2015.) $)
    lofins $p |- ph ze ps = ch ze th $=
      ( df-lofjuxt lofcmm lofsub lofsubr loftrans ) AEGZBGZECGZDGZCEGZDGMEAGZBG
      OLQBAEHIABGCDGEFJKNPDECHIK $.
  $}

  $( Extended commutativity.  (Contributed by Naip Moro, 3-Sep-2015.) $)
  lofcmmx $p  |- et ph ze ps si = et ps ze ph si $=
    ( df-lofjuxt lofcmm lofins lofsubst ) ADFBFBDFAFCEABBADABGHI $.

  $( Bounded and extended commutativity.  (Contributed by Naip Moro,
     2-Sep-2015.) $)
  lofcmmbx $p |- rh [ et ph ze ps si ] mu = rh [ et ps ze ph si ] mu $=
    ( df-lofjuxt lofid lofsubstr lofsubb1 ) ADHBHBDHAHCEFGDDABDIJK $.

  $( Double-bounded and extended commutativity.  (Contributed by Naip Moro,
     25-Feb-2017.) $)
  lofcmmbdx $p |- la [ rh [ et ph ze ps si ] mu ] ka
                  = la [ rh [ et ps ze ph si ] mu ] ka $=
    ( df-lofjuxt df-lofencl df-lofvoid lofcmmbx lofsubb1 ) FCAJDJBJEJKJGJFCBJDJ
    AJEJKJGJLLHIABCDEFGMN $.

  ${
    lofquadbx.1 $e |- ph = ps $.
    lofquadbx.2 $e |- ch = th $.
    $( Double substitution into a bounded and extended form.  (Contributed by
       Naip Moro, 3-Sep-2015.) $)
    lofquadbx $p |- rh [ et ph ze ch si ] mu = rh [ et ps ze th si ] mu $=
      ( df-lofjuxt lofquad lofins lofsubb1 ) AFLCLBFLDLEGHIACBDFABCDJKMNO $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                                 7. Axioms of LoF
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  See lof.mm for a discussion of alternate sets of axioms for LoF.  Here I
  adopt the original set of [Spencer-Brown] p. 28.  The descriptive names of
  axioms and theorems are Spencer-Brown's own.
$)

  $( Position.  Axiom J1 of [Spencer-Brown] p. 28.  (Contributed by Naip Moro,
     6-Sep-2015.) $)
  ax-lofj1 $a |- [ [ ph ] ph ] = $.

  $( Transposition.  Axiom J2 of [Spencer-Brown] p. 28.  (Contributed by Naip
     Moro, 6-Sep-2015.) $)
  ax-lofj2 $a |- [ [ ph ch ] [ ps ch ] ] = [ [ ph ] [ ps ] ] ch $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                                8. Theorems of LoF
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The theorems, which Spencer-Brown calls Consequences, are from Chapter 6 of
  [Spencer-Brown] p. 28-35.  I alter the sequence slightly, proving C5 before C4.
$)

  $( Reflexion.  Theorem C1 of [Spencer-Brown] p. 28.  (Contributed by Naip
     Moro, 6-Sep-2015.)  (Proof shortened by Naip Moro, 20-Feb-2017.) $) 
  lofc1 $p |- [ [ ph ] ] = ph $=
    ( df-lofencl df-lofjuxt df-lofvoid ax-lofj1 lofcmmbx lofsub lofsym ax-lofj2
    lofeuc lofrepbxs lofquadbx loftrans ) ABZBZOACBZNACBZCBZAOAOCBZBRONCBZDDSDD
    ONEZNOCBZTDSDDONODDDDDFOTOCZUBSCBUCOTDOUAGHNAOIJKKSPDQDDDDDAODDDDDFQDAEHLMR
    OBOCBZACAONAIUDDAOEGMM $.

  $( Generation.  Theorem C2 of [Spencer-Brown] p. 32.  (Contributed by Naip
     Moro, 6-Sep-2015.) $)
  lofc2 $p |- [ ph ps ] ps = [ ph ] ps $=
    ( df-lofencl df-lofjuxt ax-lofj2 lofc1 lofquadbx loftrans ax-lofj1 lofsubb1
    df-lofvoid lofeucr ) ACZBDZCZBCZBDCZDCZABDCBDZNRMCZPCZDCBDSMPBETAUABKKKKBAF
    BFGHROCNQKOKKKBIJNFHL $.

  $( Integration.  Theorem C3 of [Spencer-Brown] p. 32.  (Contributed by Naip
     Moro, 6-Sep-2015.) $)
  lofc3 $p |- [ ] ph = [ ] $=
    ( df-lofencl df-lofjuxt df-lofvoid lofc2 lofc1 ax-lofj1 lofbeq lofeucr ) AB
    ACZDBZACKDAEJBZBJKJFLDAGHII $.

  $( Occultation.  Theorem C4 of [Spencer-Brown] p. 33.  (Contributed by Naip
     Moro, 6-Sep-2015.)  (Proof shortened by Naip Moro, 13-Oct-2017.) $)
  lofc4 $p |- [ [ ph ] ps ] ph = ph $=
    ( df-lofencl df-lofjuxt df-lofvoid ax-lofj1 lofcmm lofsym lofrepbx lofrep
    lofc2 ) AACBDZCADZABDZCZNDCEEAMNFBADNOEEAMBAGLOBDZEAEAMPLABKHLAKIIJH $.

  $( Corollary of C4.  (Contributed by Naip Moro, 18-Sep-2015.) $)
  lofc4cor $p |- [ ph ps ] [ ph ] = [ ph ] $=
    ( df-lofencl df-lofjuxt df-lofvoid lofc1 lofsubb1 lofc4 lofeucr ) ACZCZBDCJ
    DABDCJDJKAEBEJAFGJBHI $.

  $( Iteration.  Theorem C5 of [Spencer-Brown] p. 33.  (Contributed by Naip
     Moro, 6-Sep-2015.) $)
  lofc5 $p |- ph ph = ph $=
    ( df-lofencl df-lofjuxt lofc2 df-lofvoid lofsubst loftrans ax-lofj1 lofeucr
    lofc1 ) ABZACBZACZAACZAMKBZACNKADOAEAAJFGLEEAAHFI $.

  $( Extension.  Theorem C6 of [Spencer-Brown] p. 33.  (Contributed by Naip
     Moro, 6-Sep-2015.) $)
  lofc6 $p |- [ [ ph ] [ ps ] ] [ [ ph ] ps ] = ph $=
    ( df-lofencl df-lofjuxt lofc1 df-lofvoid lofcmmbx lofquadbx ax-lofj2 lofbeq
    loftrans ax-lofj1 lofsubb1 lofeucr ) ACZBCZDCZOBDCZDZOCZASCZCZSTSEUBPCPDCZO
    DZCTUAUDUAPODCZBODCZDCUDQUERUFFFFFFOPFFFFFGOBFFFFFGHPBOIKJUCFFOFFPLMKNAEK
    $.

  $( Corollary of C6.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  lofc6cor $p |- [ [ ph ] ps ] [ ph ps ] = [ ps ] $=
    ( df-lofjuxt df-lofvoid df-lofencl lofcmm lofc1 lofc6 lofrepbx ) BACZABCDDA
    EZBCZEDBEZBAFBKCZLDDDJEMBKFMEZBDANEDMBGZOBDKDOACEMPMAHIIII $.

  $( Echelon.  Theorem C7 of [Spencer-Brown] p. 34.  (Contributed by Naip Moro,
     6-Sep-2015.) $)
  lofc7 $p |- [ [ [ ph ] ps ] ch ] = [ ph ch ] [ [ ps ] ch ] $=
    ( df-lofjuxt df-lofencl ax-lofj2 df-lofvoid lofc1 lofsubb1 loftrans lofeucr
    lofbeq ) ACDEBEZCDEDZEZEZAEZBDECDZEZNPQMEZDECDZESOUAAMCFLUARTBQGGCBHILJNHK
    $.

  $( Modified transposition.  Theorem C8 of [Spencer-Brown] p. 34.
     (Contributed by Naip Moro, 6-Sep-2015.) $)
  lofc8 $p |- [ [ ph ] [ ps th ] [ ch th ] ]
             = [ [ ph ] [ ps ] [ ch ] ] [ [ ph ] [ th ] ] $=
    ( df-lofencl df-lofjuxt df-lofvoid lofc1 ax-lofj2 lofsubb2 lofrepbx lofquad
    lofbeq lofc7 lofcmmbx loftrans ) AEZBDFEZFCDFEZFEBEZCEZFZEDFZEZQFEZQTFUAFEZ
    QDEZFEZFZRSFZEZEZUJQGGGUEUJHULUDQGGGUKUCBCDIMJKUEUBQFEZUGQFEZFUIUBDQNUMUFUN
    UHUBQGGGGGOUGQGGGGGOLPP $.

  $( Crosstransposition.  Theorem C9 of [Spencer-Brown] p. 35.  (Contributed by
     Naip Moro, 6-Sep-2015.) $)
  lofc9 $p |- [ [ [ ps ] [ ph ] ] [ [ ch ] [ ph ] ]
              [ [ th ] ph ] [ [ ta ] ph ] ]
              = [ [ ph ] ps ch ] [ ph th ta ] $=
    ( df-lofencl df-lofjuxt df-lofvoid lofc1 ax-lofj2 lofquadbx loftrans lofbeq
    lofeucr lofsubb2 lofc8 lofsubb1 lofc2 lofcmmbx lofc6 ) BFZAFZGFZCFZUBGFZGZD
    FZAGFZGEFZAGFZGFDEGZFZAGZFZUCGUEGFZUBBGCGFZADGEGFZGZUHUJGZUNUFHHHUSFZFUSUNU
    SIUTUMUTUGFZUIFZGFAGUMUGUIAJVADVBEHHHHADIEIKLMNOUOUNBGCGZFZUKAGFZGZURUOVDUL
    FZAGZFGZVFUOVDUNAGZFGZVIUOVDUNUBFZGFZGZVKUOUNUAFZGUDFZGFVMGVNUMUAUDUBPVOBVP
    CUNHHHVMBICIKLVLAUNHVDHAIZQLVJVHHHVDHULARQLVGUKHAVDHUKIQLVCVEGFVEGZVFURVCVE
    RVRAULGFZBGCGZUQGFVEGZURUNVSVEUQHBCGZHHVEULAHHHHHSUKAHHHHHSKVLULGFZBGCGZVLD
    GEGFZGFVEGZWAURWDVTWEUQHHHHVEVLAHULHWBVQQVLAHUKHHVQQKWFWCWEGZBGCGFVEGZURWBW
    EWCHHHVESWHUPVEGURWGUBHWBHVEUBUKTQUKAHHHUPHSLLNLNLL $.

  $( The following two equations (or rules of calculation) constitute the
     entire Primary Arithmetic which underlies the Primary Algebra, so are
     conceptually prior to the axioms and theorems.  LoF, and hence
     propositional logic, is nothing but a prolonged deduction from this pair
     of arithmetical identities.
  $)

  $( Number.  Rule I1 of [Spencer-Brown] p. 12.  (Contributed by Naip Moro,
     14-Feb-2017.) $)
  lofi1 $p |- [ ] [ ] = [ ] $=
    ( df-lofvoid df-lofencl lofc5 ) ABC $.

  $( Order.  Rule I2 of [Spencer-Brown] p. 12.  (Contributed by Naip Moro,
     14-Feb-2017.) $)
  lofi2 $p |- [ [ ] ] = $=
    ( df-lofvoid ax-lofj1 ) AB $.

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

  $( ~ lofc1 reversed.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  lofc1r $p |- ph = [ [ ph ] ] $=
    ( df-lofencl lofc1 lofsym ) ABBAACD $.

  $( ~ lofc1 extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  lofc1x $p |- et [ [ ph ] ] ze = et ph ze $=
    ( df-lofencl lofc1 lofsubst ) ADDABCAEF $.

  $( ~ lofc1 reversed and extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  lofc1rx $p |- et ph ze = et [ [ ph ] ] ze $=
    ( df-lofencl lofc1r lofsubst ) AADDBCAEF $.

  $( ~ lofc1 bounded and extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  lofc1bx $p |- si [ et [ [ ph ] ] ze ] rh = si [ et ph ze ] rh $=
    ( df-lofencl df-lofjuxt df-lofvoid lofc1x lofsubb1 ) BAFFGCGBAGCGHHDEABCIJ
    $.

  $( ~ lofc1 reversed, bounded, and extended.  (Contributed by Naip Moro,
     14-Feb-2017.) $)
  lofc1rbx $p |- si [ et ph ze ] rh = si [ et [ [ ph ] ] ze ] rh $=
    ( df-lofencl df-lofjuxt lofc1bx lofsym ) DBAFFGCGFGEGDBAGCGFGEGABCDEHI $.

  $( Generalizations of C2. $)

  $( ~ lofc2 extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  lofc2x $p |- et [ ph ps ze ] si ps rh = et [ ph ze ] si ps rh $=
    ( df-lofjuxt df-lofencl lofcmm df-lofvoid lofcmmbx lofcmmx loftrans lofsym
    lofc2 lofrep ) CADGZHZGZEGBGFGCABGDGHGEGBGFGZBEGEBGZSFTBEIQBGHZBGRBGCEFGTQB
    OTCUBGZBGEGFGZTUCEGBGFGUDBDAJJCUAFGKEBUCJFLMNPPN $.

  $( ~ lofc2 bounded and extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  lofc2bx $p |- mu [ et [ ph ps ze ] si ps rh ] la
                = mu [ et [ ph ze ] si ps rh ] la $=
    ( df-lofjuxt df-lofencl df-lofvoid lofc2x lofsubb1 ) CABIDIJIEIBIFICADIJIEI
    BIFIKKGHABCDEFLM $.

  $( ~ lofc2 reversed and extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  lofc2rx $p |- et ps ze [ ph ps si ] rh = et ps ze [ ph si ] rh $=
    ( df-lofjuxt df-lofencl df-lofvoid lofcmmx lofc2x loftrans ) CBGDGZABGEGHZG
    FGZCAEGHZGBGDGFGZMPGFGOCNGBGDGFGQBDGZNCIFJABCEIDFGKLPRCIFJL $.

  $( ~ lofc2 reversed, bounded, and extended.  (Contributed by Naip Moro,
     14-Feb-2017.) $)
  lofc2rbx $p |- mu [ et [ ph ze ] si ps rh ] la
                 = mu [ et [ ph ps ze ] si ps rh ] la $=
    ( df-lofjuxt df-lofencl lofc2bx lofsym ) GCABIDIJIEIBIFIJIHIGCADIJIEIBIFIJI
    HIABCDEFGHKL $.

  $( ~ lofc2 special case.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  lofc2e $p |- et [ ph ] ze ph si = [ ] $=
    ( df-lofencl df-lofjuxt df-lofvoid lofc2x lofcmmx lofc3 loftrans ) BAEFCFAF
    DFBGEZFCFAFDFZLGABGCDHMLBFCFAFDFLBLGGCAFDFIBCFAFDFJKK $.

  $( Generalizations of C3. $)

  $( ~ lofc3 extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  lofc3x $p |- ph [ ] ps = [ ] $=
    ( df-lofvoid df-lofencl df-lofjuxt lofcmm lofc3 loftrans ) ACDZEBEIBEZAEIAJ
    FBAEGH $.

  $( ~ lofc3 bounded and extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  lofc3bx $p |- et [ ph [ ] ps ] ze = et ze $=
    ( df-lofvoid df-lofencl df-lofjuxt lofc3x lofsubb1 lofc1x loftrans ) CAEFZG
    BGZFGDGCLFGDGCDGMLEECDABHIECDJK $.

  $( Generalizations of C4. $)

  $( ~ lofc4 extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  lofc4x $p |- si [ et [ ph ] ze ] rh ph mu = si ph rh mu $=
    ( df-lofencl df-lofjuxt lofcmmbx lofcmmx loftrans lofc4 lofid lofrep lofeuc
    df-lofvoid ) DBAGZHCHGHEHAHFHZDQBHCHGZHZAHEHFHZDAHEHFHRTEHAHFHUABQPPCDEAHFH
    IEATPFJKSAHADEFHUAABCHLUAMNO $.

  $( ~ lofc4 reversed and extended. (Contributed by Naip Moro, 14-Feb-2017.) $)
  lofc4rx $p |- si ph rh mu = si [ et [ ph ] ze ] rh ph mu $=
    ( df-lofencl df-lofjuxt lofc4x lofsym ) DBAGHCHGHEHAHFHDAHEHFHABCDEFIJ $.

  $( Generalizations of C5. $)

  $( ~ lofc5 extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  lofc5x $p |- et ph ze ph si = et ph ze si $=
    ( df-lofjuxt df-lofvoid lofcmmx lofc5 lofid lofrep lofeuc ) BAEZCEZAEDELAEC
    EDEZMDECALFDGAAEABCDENAHNIJK $.

  $( ~ lofc5 bounded and extended.  (Contributed by Naip Moro, 25-Feb-2017.) $)
  lofc5bx $p |- rh [ et ph ze ph si ] mu = rh [ et ph ze si ] mu $=
    ( df-lofjuxt df-lofvoid lofc5x lofsubb1 ) BAGCGZAGDGKDGHHEFABCDIJ $.

  $( ~ lofc5 reversed and extended. (Contributed by Naip Moro, 14-Feb-2017.) $)
  lofc5rx $p |- et ph ze si = et ph ze ph si $=
    ( df-lofjuxt lofc5x lofsym ) BAECEZAEDEHDEABCDFG $.

  $( Generalizations of C6. $)

  $( ~ lofc6 extended.  (Contributed by Naip Moro, 25-Feb-2017.) $)
  lofc6x $p |- et [ [ ph ] [ ps ] ] ze [ [ ph ] ps ] si = et ph ze si $=
    ( df-lofencl df-lofjuxt lofc6 df-lofvoid lofcmmx lofreps ) AFZBFGFZLBGFZGAC
    DEGCMGZDGNGEGABHDNOIEJK $.

  $( ~ lofc6 reversed and extended. (Contributed by Naip Moro, 25-Feb-2017.) $)
  lofc6rx $p |- et [ [ ph ] ps ] ze [ [ ph ] [ ps ] ] si = et ph ze si $=
    ( df-lofencl df-lofjuxt lofcmmx lofc6x loftrans ) CAFZBGFZGDGKBFGFZGEGCMGDG
    LGEGCAGDGEGLMCDEHABCDEIJ $.

  $( Generalizations of J1. $)

  $( ~ ax-lofj1 extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  lofj1x $p |- rh [ et [ ph ] ze ph si ] mu = rh mu $=
    ( df-lofencl df-lofjuxt df-lofvoid lofc2bx lofc3bx loftrans ) EBAGHCHAHDHGH
    FHEBIGHCHAHDHGHFHEFHIABICDEFJBCAHDHEFKL $.

  $( ~ ax-lofj1 reversed and extended.  (Contributed by Naip Moro,
     25-Feb-2017.) $)
  lofj1rx $p |- rh [ et ph ze [ ph ] si ] mu = rh mu $=
    ( df-lofjuxt df-lofencl lofcmmbx lofj1x loftrans ) EBAGCGAHZGDGHGFGEBLGCGAG
    DGHGFGEFGALBCDEFIABCDEFJK $.

  $( ~ ax-lofj1 extended and switched.  (Contributed by Naip Moro,
     14-Feb-2017.) $)
  lofj1xs $p |- rh mu = rh [ et [ ph ] ze ph si ] mu $=
    ( df-lofencl df-lofjuxt lofj1x lofsym ) EBAGHCHAHDHGHFHEFHABCDEFIJ $.

  $( Generalizations of J2. $)

  $( ~ ax-lofj2 extended.  (Contributed by Naip Moro, 14-Feb-2017.) $)
  lofj2x $p |- et [ [ ph ch ] [ ps ch ] ] ze si
               = et [ [ ph ] [ ps ] ] ze ch si $=
    ( df-lofjuxt df-lofencl ax-lofj2 lofsubst df-lofvoid lofcmmx loftrans ) DAC
    GHBCGHGHZGEGFGDAHBHGHZGZCGEGFGPEGCGFGNOCGDEFGABCIJCEPKFLM $.

  $( ~ ax-lofj2 reversed and extended.  (Contributed by Naip Moro,
     14-Feb-2017.) $)
  lofj2rx $p |- et [ [ ph ] [ ps ] ] ze ch si
                = et [ [ ph ch ] [ ps ch ] ] ze si $=
    ( df-lofjuxt df-lofencl lofj2x lofsym ) DACGHBCGHGHGEGFGDAHBHGHGEGCGFGABCDE
    FIJ $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                          10. Excursion into equality
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( We will later define ` ( ph -> ps ) ` as ` [ ph ] ps ` .  In that light,
     this theorem shows that our previous definition of equality is equivalent
     to ` ( ( ph -> ps ) /\ ( ps -> ph ) ) ` .  The latter, in turn, is what we
     mean by the biconditional ` <-> ` .  In other words, equality and the
     biconditional are, as expected, equivalent.  (Contributed by Naip Moro,
     24-Feb-2017.) $)
  lofbiimp $p |- [ [ [ ph ] ps ] [ [ ps ] ph ] ]
                 = [ [ ph ] [ ps ] ] [ ph ps ] $=
    ( df-lofencl df-lofjuxt df-lofvoid lofcmm lofsubbd1 lofc1 lofsubb1 lofcmmbx
    lofc6 lofc9 lofeucr ) BACZDZCBCZADCZDCZNBDZCQDCNPDCABDCDZOSEEEQEEBNFGPCZNDC
    ZQDZCZRTUABENEQEEBHGECZNDCZUEADCZDZUBDQDCZUDTUHEEUCEEEAKIUFUBDQDUGDCUITUCUG
    UFEEEEJAEPBELMMMM $.

  $( We next prove that equality, and hence the biconditional, are
     associative.  First, four preliminary theorems. $)

  $( Lemma.  (Contributed by Naip Moro, 24-Feb-2017.) $)
  lofbiasslem1 $p |- [ ps [ ph ps ] ch ] = [ [ ph ] ps ch ] $=
    ( df-lofjuxt df-lofencl df-lofvoid lofcmmbx lofc2bx loftrans ) BABDEZDCDEJB
    DCDEAEBDCDEBJFFCFFGABFFFCFFHI $.

  $( Lemma.  (Contributed by Naip Moro, 24-Feb-2017.) $)
  lofbiasslem2 $p |- [ ph [ ph ps ] ch ] = [ ph [ ps ] ch ] $=
    ( df-lofjuxt df-lofencl df-lofvoid lofcmmbdx lofbiasslem1 loftrans lofcmmbx
    ) AABDEDCDEZBEZADCDEZALDCDEKABADEDCDEMABFFFACFFGBACHILAFFCFFJI $.

  $( Let ` P = [ [ ph ] [ ps ] ] [ ph ps ] ` and
     ` Q = [ [ ps ] [ ch ] ] [ ps ch ] ` .  Proving that equality/biconditional
     associates amounts to proving:
     ` [ [ P ] [ ch ] ] [ P ch ] = [ [ ph ] [ Q ] ] [ ph Q ] ` which is
     demonstrated in ~ lofbiass .  Meanwhile, this theorem shows that the lhs
     of the latter equation evaluates to a form symmetric in the three
     variables, informal evidence for associativity.  (Contributed by Naip Moro,
     24-Feb-2017.) $)
  lofbiass3 $p |- [ [ [ [ ph ] [ ps ] ] [ ph ps ] ] [ ch ] ]
                  [ [ [ ph ] [ ps ] ] [ ph ps ] ch ]
                  = [ [ ph ] [ ps ] [ ch ] ] [ ph ps [ ch ] ]
                     [ ph [ ps ] ch ] [ [ ph ] ps ch ] $=
    ( df-lofencl df-lofjuxt ax-lofj2 lofbeq lofc1 lofeucr lofbiasslem2 lofsubst
    lofquad loftrans lofbiasslem1 lofsubr ) ADZBDZEZDABEZDZEZDCDZEZDZUACEZDZEZR
    UBEDSUBEDEZAQECEDZEZBTECEDZEUJPBECEDZEUGUHATECEDZUKEZEUHUIUKEEUDUHUFUNUHDZD
    UDUHUOUCRSUBFGUHHIUNDZDUFUNUPUEABTCEFGUNHILUMUIUHUKABCJKMUKULUJABCNOM $.

  $( A permuted version of ~ lofbiass3 .  (Contributed by Naip Moro,
     29-Dec-2016.) $)
  lofbiass3p $p |- [ [ [ [ ps ] [ ch ] ] [ ps ch ] ] [ ph ] ]
                   [ [ [ ps ] [ ch ] ] [ ps ch ] ph ]
                   = [ [ ph ] [ ps ] [ ch ] ] [ ph ps [ ch ] ]
                      [ ph [ ps ] ch ] [ [ ph ] ps ch ] $=
    ( df-lofencl df-lofjuxt lofbiass3 df-lofvoid lofcmmbx loftrans lofcmmx ) BD
    ZCDZEZDBCEZDEZDADZEDOAEDEZPKELEDZPBECEDZEZAKECEDZEABELEDZEZRUBEUAESEQTUBEZU
    AEZUCQUDKCEZAEDZEZUEQTBLEZAEDZEUGEZUHQRNPEDZEUJEUGEZUKQMPEDULEUJEUGEUMBCAFM
    PGGGGULUJEUGEHINPGGGRUJUGEHIUIAGGGTUGHIUFAGGGUDGHIUBUATGGJISUBRUAGJI $.

  $( Proving the associativity of equality/biconditional.  (Contributed by
     Naip Moro, 29-Dec-2016.) $)
  lofbiass $p |- [ [ [ [ ph ] [ ps ] ] [ ph ps ] ] [ ch ] ]
                  [ [ [ ph ] [ ps ] ] [ ph ps ] ch ]
                  = [ [ ph ] [ [ [ ps ] [ ch ] ] [ ps ch ] ] ]
                     [ ph [ [ ps ] [ ch ] ] [ ps ch ] ] $=
    ( df-lofencl df-lofjuxt lofbiass3 lofbiass3p df-lofvoid lofcmmbx loftrans
    lofeuc ) ADZBDZEZDABEZDEZDCDZEDPCEDEZMQEDZBCEDZEZDZLEDUAAEDZEZLUBEDZASETEDE
    ZRNQEDOQEDEAMECEDELBECEDEUDABCFABCGKUDUEUCEUFUBLHHHHUCIUAAHHHUEHIJJ $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              11.  A bridge between LoF and classical logic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( The Equanimity axiom.  This rule is the key that allows us to interchange
     equational and classical forms.  $)
  ${
    ax-lofqny.1 $e |- ph $.
    ax-lofqny.2 $e |- ph = ps $.
    $( If we assert both ` ph ` and that ` ph ` is equal to ` ps ` , we can
       infer ` ps ` .  (Contributed by Naip Moro, 14-Feb-2017.) $)
    ax-lofqny $a |- ps $.
  $}

  $( This important theorem states that the equivalence of ` ph ` to true is
     equivalent to just ` ph ` .  (Contributed by Naip Moro, 29-Jan-2017.) $)
  lofelimeq $p |- [ [ ph ] [ [ ] ] ] [ ph [ ] ] = ph $=
    ( df-lofencl df-lofvoid lofi2 lofsubb1 lofc1 lofsubst loftrans lofcmm lofc2
    df-lofjuxt lofcmmbx ) ABZCBZBZKBANKBZKZOAKZAQNAKBZAKZRQASKZTQAPKZUAQMBZPKUB
    OCMCCPDEUCACPAFGHANCCCACLHASIHNAJHOCCADGH $.

  $( Truth equivalence elimination.  $)
  ${
    lofelim.1 $e |- ph = [ ] $.
    $( If ` ph ` is equivalent to true, we can infer ` ph ` .  (Contributed by
       Naip Moro, 14-Feb-2017.) $)
    lofelim $p |- ph $=
      ( df-lofencl df-lofvoid df-lofjuxt df-lofequ lofelimeq ax-lofqny ) ACDCZC
      ECAIECEAAIBFAGH $.
  $}

  $( Truth equivalence introduction.  $)
  ${
    lofintr.1 $e |- ph $.
    $( If we can assert ` ph ` , then we can infer that ` ph ` is equivalent to
       true.  (Contributed by Naip Moro, 14-Feb-2017.) $)
    lofintr $p |- ph = [ ] $=
      ( df-lofvoid df-lofencl df-lofjuxt lofelimeq lofsym ax-lofqny df-lofuni )
      ACDZAADJDEDAJEDEZBKAAFGHI $.
  $}

  ${
    lofeucrelim.1 $e |- ph = ps $.
    lofeucrelim.2 $e |- ph = [ ] $.
    $( Eliminate equation from ~ lofeucr deduction.  (Contributed by Naip Moro,
       14-Feb-2017.) $)
    lofeucrelim $p |- ps $=
      ( df-lofvoid df-lofencl lofeucr lofelim ) BABEFCDGH $.
  $}

  ${
    loftranselim.1 $e |- ph = ps $.
    loftranselim.2 $e |- ps = [ ] $.
    $( Eliminate equation from ~ loftrans deduction.  (Contributed by Naip
       Moro, 14-Feb-2017.) $)
    loftranselim $p |- ph $=
      ( df-lofvoid df-lofencl loftrans lofelim ) AABEFCDGH $.
  $}

  ${
    lofand.1 $e |- ph $.
    lofand.2 $e |- ps $.
    $( Wrap premises in LoF conjunctive form.  From ` ph ` and ` ps ` we infer
       the LoF equivalent of ` ph /\ ps ` .  (Contributed by Naip Moro,
       14-Feb-2017.) $)
    lofand $p |- [ [ ph ] [ ps ] ] $=
      ( df-lofencl df-lofjuxt lofc3bx lofintr lofeuc df-lofequ lofrepbx lofeucr
      df-lofvoid lofelim ) AEBEFEZOMEZBFEFOPMBOMGAPMBOMPACHZOABFEFABAPBQBDHIJHK
      LN $.
  $}

  ${
    lofeq.1 $e |- ph $.
    lofeq.2 $e |- ps $.
    $( From assertions of ` ph ` and ` ps ` we infer their equality.
       (Contributed by Naip Moro, 1-Mar-2017.) $)
    lofeq $p |- ph = ps $=
      ( df-lofvoid df-lofencl lofintr lofeuc ) AEFBACGBDGH $.
  $}

  ${
    lofmp.1 $e |- ph $.
    lofmp.2 $e |- [ ph ] ps $.
    $( LoF version of modus ponens. (Contributed by Naip Moro, 14-Feb-2017.) $)
    lofmp $p |- ps $=
      ( df-lofencl df-lofvoid lofintr lofbeq loftrans df-lofjuxt lofrep lofelim
      lofc1 ) BAEZFFBFEZNOEFAOACGHFMINBJDGKL $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   12. Defining classical propositional logic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  We define ` ( ph -> ps ) ` as ` [ ph ] ps ` and ` -. ph ` as ` [ ph ] ` ,
  consistent with our interpretation of ` [ ] ` as true and the void as false,
  and determining the interpretation of the other logical constants:

  <HTML><br></HTML>

  <HTML><ul>
  <li> ` -. ph = [ ph ] ` .</li>
  <li> ` ( ph -> ps ) = [ ph ] ps ` .</li>
  <li> ` ( ph \/ ps ) = ph ps ` .</li>
  <li> ` ( ph /\ ps ) = [ [ ph ] [ ps ] ] ` .</li>
  <li> ` ( ph <-> ps ) = [ [ ph ] [ ps ] ] [ ph ps ] ` .</li>
  </ul></HTML>

  (NOTE:  LoF is "self-dual".  If we interpret ` [ ] ` as false and the void as
  true, the theorems of LoF remain valid but carry different meanings:

  <HTML><br></HTML>

  <HTML><ul>
  <li> ` -. ph = [ ph ] ` .</li>
  <li> ` ( ph -> ps ) = [ ph [ ps ] ] ` .</li>
  <li> ` ( ph \/ ps ) = [ [ ph ] [ ps ] ] ` .</li>
  <li> ` ( ph /\ ps ) = ph ps ` .</li>
  <li> ` ( ph <-> ps ) = [ [ [ ph ] [ ps ] ] [ ph ps ] ] ` .</li>
  </ul></HTML>

  This is C. S. Peirce's remarkable "alpha" system from his existential graphs,
  the first modern instance of a boundary algebra.)

  Constructing hybrid wffs like ` [ -. ph ] ` that lack meaning in either LoF
  or propositional logic becomes not merely possible but necessary in the
  course of translating from one system to the other.  Indeed, one can validly
  calculate with these hybrid forms.  For example, ` [ -. ph ] -. ph ` can
  be reduced to ` [ ] ` by ~ lofc2e without the need to fully translate into
  LoF.  The proof of ~ df-bi makes full use of that possibility.
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

  $( Define material implication in terms of LoF. (Contributed by Naip Moro,
     27-Feb-2017.) $)
  df-lofimp $a |- ( ph -> ps ) = [ ph ] ps $.

  $( Define negation in terms of LoF. (Contributed by Naip Moro,
     27-Feb-2017.) $)
  df-lofneg $a |- -. ph = [ ph ] $.

  $( Express the negation of an implication.  (Contributed by Naip Moro,
     27-Feb-2017.) $)
  lofni $p |- -. ( ph -> ps ) = [ [ ph ] ps ] $=
    ( wi df-lofencl df-lofjuxt df-lofvoid wn df-lofimp df-lofneg lofrepbxs ) AB
    CZADBEFFFFKGABHKIJ $.

  $( A hybrid theorem.  Enclosing the negation of a proposition is equivalent
     to the proposition.  (Contributed by Naip Moro, 28-Feb-2017.) $)
  lofne $p |- [ -. ph ] = ph $=
    ( wn df-lofencl df-lofneg lofbeq lofc1 loftrans ) ABZCACZCAHIADEAFG $.

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

  $( LoF version of set.mm's ~ pm2.18.  Law of Clavius.  (Contributed by Naip
     Moro, 14-Feb-2017.) $)
  lofclav $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wn wi df-lofencl df-lofjuxt df-lofneg df-lofimp lofrepbxs lofc2x loftrans
    df-lofvoid lofc1x lofreps lofc2e lofelim ) ABZACZACZRADZAEKDPSKARAFRPDZAEZD
    AEZPAEZQUAKKKARPAGQAGHUBTDAEUCTAKKKKIPKALJJMAKKKNJO $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
               14.  Proving the axioms of propositional logic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  In this section we prove the three axioms of set.mm's propositional calculus,
  as well as modus ponens.  This completes the task of demonstrating LoF's
  ability to ground the formalization of mathematics.
$)

  $( Proving set.mm's axiom ~ ax-1 as a theorem.  (Contributed by Naip Moro,
     14-Feb-2017.) $)
  ax-1 $p |- ( ph -> ( ps -> ph ) ) $=
    ( wi df-lofencl df-lofjuxt df-lofvoid df-lofimp lofsubr loftrans lofelim
    lofc2e ) ABACZCZMADZBDZEAEZFDMNLEPALGLOAENBAGHIAFOFKIJ $.

  $( Proving set.mm's axiom ~ ax-2 as a theorem.  (Contributed by Naip Moro,
     14-Feb-2017.) $)
  ax-2 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    ( df-lofencl df-lofjuxt df-lofimp lofreps lofrepbxs lofc2x loftrans lofcmmx
    wi df-lofvoid lofc2e lofelim ) ABCLZLZABLZACLZLZLZUAADZBDZECEZDZUBEUCECEZMD
    UAUEUCEUBECEZUFUAUEUBBEZDZEUBECEUGPUCCEUBMMUIUBECEZUABCFQUBPEMMMUJUAAPFRUHM
    MQDZUBCEZUAABFSULUKRDZEMUAACFTUMSEUKMUARSFQTFGGHHHMUBUEBMCIJUCUBUEMCKJUDMMM
    NJO $.

  $( Proving set.mm's axiom ~ ax-3 as a theorem.  (Contributed by Naip Moro,
     14-Feb-2017.) $)
  ax-3 $p |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $=
    ( wn wi df-lofencl df-lofjuxt df-lofvoid df-lofneg lofbeq df-lofimp lofreps
    lofrepbxs lofc2x loftrans lofc1bx lofc2e lofelim ) ACZBCZDZBADZDZUBAEZBEZFA
    FZGEUBUCEZEUDFAFZUEUBUFUDFEUDFAFUGSUDUFGGUDAFZUBBHREZUFGSGUHUBRUCAHITUISFGG
    GUHUBRSJUAUHTEGUBBAJTUAJKLLLUFUDGGGAMNAGGGUHONAGUDGPNQ $.

  ${
    $( Minor premise for modus ponens. $)
    min $e |- ph $.
    $( Major premise for modus ponens. $)
    maj $e |- ( ph -> ps ) $.
    $( Proving set.mm's modus ponens ~ ax-mp as a theorem.  (Contributed by
       Naip Moro, 14-Feb-2017.) $)
    ax-mp $p |- ps $=
      ( df-lofencl df-lofjuxt wi df-lofvoid df-lofimp lofintr lofeucr lofelim
      lofmp ) ABCAEBFZABGZNHEABIODJKLM $.
  $}

  $( With the proofs of ~ ax-1 , ~ ax-2 , ~ ax-3 , and ~ ax-mp completed, we
     can retire LoF and proceed with the classical development of metamath's
     logic.  But first, a foray into the theory of the biconditional. $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                            15.  The biconditional
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  set.mm's section on the biconditional begins with the definition ~ df-bi :
  ` -. ( ( ( ph <-> ps ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )
    -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) ) `
  followed by three theorems that depend on it:   ~ impbi , ~ biimp  and
  ~ dfbi1 .  Here we utilize the equivalence of the biconditional with equality
  to prove all four of those statements, including the definition, directly
  from LoF.

  In examining this section, the reader may wonder about the need for the
  equality sign, and in fact we could have dispensed with it, replacing ` = `
  with ` <-> ` right from the start.  I retained it for readability and to
  avoid some nuanced distinctions.  For example, while ` ( ph <-> ps ) ` is a
  wff, ` ph = ps ` cannot be one without introducing contradiction (see
  Appendix A for details).
$)

  $( Declare the biconditional symbol. $)
  $c <-> $.

  $( The biconditional is a wff. $)
  wb $a wff ( ph <-> ps ) $.

  $( A definition of the biconditional in terms of LoF equality.  (Contributed
     by Naip Moro, 21-Feb-2017.) $)
  df-lofbi $a |- ( ph <-> ps ) = [ [ ph ] [ ps ] ] [ ph ps ] $.

  $( A more traditional understanding of the biconditional as (the LoF
     equivalent of) a conjunction of converse implications.  (Contributed by
     Naip Moro, 24-Feb-2017.) $)
  lofbii $p |- ( ph <-> ps ) = [ [ [ ph ] ps ] [ [ ps ] ph ] ] $=
    ( wb df-lofencl df-lofjuxt df-lofbi lofbiimp lofeuc ) ABCADZBDZEDABEDEIBEDJ
    AEDEDABFABGH $.

  ${
    lofbieq.1 $e |- ( ph <-> ps ) $.
    $( Infer an equality from a biconditional.  (Contributed by Naip Moro,
       24-Feb-2017.) $)
    lofbieq $p |- ph = ps $=
      ( wb df-lofencl df-lofjuxt df-lofbi ax-lofqny df-lofuni ) ABABDAEBEFEABFE
      FCABGHI $.
  $}

  ${
    lofeqbi.1 $e |- ph = ps $.
    $( Infer a biconditional from an equality.  (Contributed by Naip Moro,
       4-Mar-2017.) $)
    lofeqbi $p |- ( ph <-> ps ) $=
      ( df-lofencl df-lofjuxt wb df-lofequ df-lofbi lofsym ax-lofqny ) ADBDEDAB
      EDEZABFZABCGLKABHIJ $.
  $}

  ${
    lofeqi.1 $e |- ph = ps $.
    $( Infer an implication from an equality.  (Contributed by Naip Moro,
       28-Feb-2017.) $)
    lofeqi $p |- ( ph -> ps ) $=
      ( df-lofencl df-lofjuxt df-lofvoid lofbeq lofsub lofc2e lofelim df-lofimp
      wi loftrans lofsym ax-lofqny ) ADZBEZABLZQQBDZBEFDPSBABCGHBFFFIMJRQABKNO
      $.
  $}

  $( Relating the biconditional connective to primitive connectives, proved
     directly from LoF. (Contributed by Naip Moro, 25-Feb-2017.) $)
  lofbi1 $p |- ( ph <-> ps ) = -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) $=
    ( wb df-lofencl df-lofjuxt wi lofbii df-lofneg df-lofvoid lofsubb1 loftrans
    wn df-lofimp lofsubbd1 lofeuc ) ABCADBEZDZBDAEZDEDZABFZBAFZLZFZLZABGUDQUADZ
    EDZSUDTDZUEEDZUFUDUGUBEZDZUHUDUCDUJUCHUCUIIIIITUBMJKUBUEUGIIIUAHJKTPIIIUEII
    ABMNKUARIIQIIIBAMNKO $.

  $( The reverse of ~ lofbi1 .  (Contributed by Naip Moro, 26-Feb-2017.) $)
  lofbi1r $p |- -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) = ( ph <-> ps ) $=
    ( wb wi wn lofbi1 lofsym ) ABCABDBADEDEABFG $.

  $( Relating the biconditional connective to primitive connectives, proved
     directly from LoF. (Contributed by Naip Moro, 4-Mar-2017.) $)
  dfbi1 $p |- ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $=
    ( wb wi wn lofbi1 lofeqbi ) ABCABDBADEDEABFG $.

  $( Property of the biconditional connective proved directly from LoF.
     (Contributed by Naip Moro, 24-Feb-2017.) $)
  biimp $p |- ( ( ph <-> ps ) -> ( ph -> ps ) ) $=
    ( wb wi df-lofencl df-lofjuxt df-lofvoid lofj1rx df-lofbi df-lofimp lofreps
    lofrepbxs lofj2rx loftrans lofc1x lofc2e lofelim ) ABCZABDZDZTAEZBEFZUAFZBF
    ZGETUCEZEBFUDABFZUAFEZGUEGGBTAGBGGGHTUBEUFEFZEUAFBFUEUGFEBFRUHGGGUABFZTABIS
    UIREGTABJRSJKLUBUFUAGGBMNLUCGBONBUAUAGPNQ $.

  $( Property of the biconditional connective proved directly from LoF.
     (Contributed by Naip Moro, 24-Feb-2017.) $)
  impbi $p |- ( ( ph -> ps ) -> ( ( ps -> ph ) -> ( ph <-> ps ) ) ) $=
    ( wi wb df-lofencl df-lofjuxt df-lofvoid lofsubr loftrans df-lofbi lofsubb1
    df-lofimp lofc6rx lofc2rx lofcmm lofc2e lofelim ) ABCZBACZABDZCZCZUBBEZAFZE
    ZUCFZAFZGEUBAUEFZUCFZUGUBUHABFEZFZUIUBAEZBFZEZUEFULUCFEUJFZFZUKUBUNSEZFUOFZ
    UPUBREZUQFZUOFZURUBUTTFZVAUBUSUAFVBRUALUAUQTFUSSTLHITUOUTABJHIRUMGGGUQUOFAB
    LKISUDGGUNUOBALKIABGUEUJMIGAGUEBGNIAUFOIUDGGGPIQ $.

  $( The biconditional definition proved as a theorem directly from LoF.
     (Contributed by Naip Moro, 28-Feb-2017.) $)
  df-bi $p |- -. ( ( ( ph <-> ps ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )
        -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $=
    ( wb df-lofencl df-lofjuxt df-lofvoid lofbi1r ax-lofj1 df-lofimp lofrepbdxs
    wi wn lofni lofrepbxs lofne loftrans lofc2e lofelim ) ABCZABKBAKLKLZKZTSKZL
    ZKLZUDSDZSEZFDTSFFFSUDABGZUDUBTDSEUDUCDUBUFDFFUCFFUDSHTSUEFFUCFFUDUGUAUETEF
    FFUCFFUDSTIUAUCMJJNUBOPTSIPNSFFFQPR $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                                16.  Conclusion
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  To show that this file can replace set.mm's classical logic, remove (or
  comment out) the following sections of set.mm:
    *  Pre-logic.
    *  Recursively define primitive wffs for propositional calculus.
    *  The axioms of propositional calculus.

  and remove (or comment out) the following statements:
    *  the declaration of the constants: "[", "]", "=", and "<->".
    *  ~ wb , ~ df-bi ,  ~ impbi ,  ~ biimp , ~ dfbi1 .

  Now either:  1) Paste the contents of this file anywhere before the start of
  set.mm's active statements, or 2) Add "$[ lofset.mm $]" to the beginning of
  set.mm (making sure lofset.mm is in the same directory as set.mm).  Read the
  ensuing (saved) file into metamath and run the command "verify proof *".
  Expected result:  "All proofs in the database were verified".

  An example of such an altered set.mm file (via option 1) is available here:
  ~ https://github.com/naipmoro/lofmm/blob/master/setx.mm .

  This file has been tested with the develop branch
  (commit 175c5668cd2e509c8d8118f1e442ebb8eeb8f8a7 dated 15-Mar-2021) available
  at ~ https://github.com/metamath/set.mm/raw/develop/set.mm .
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                                 Appendix A
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Another important difference between LoF and equational logic: the latter
  allows forms such as ` ph = ph = [ ] ` and ` [ ph ] = ph = ` by ascribing
  well-formedness to binary equations, while in LoF this would result in
  contradiction, as demonstrated by the following (commented out) derivation.

  @( Assume equality can be part of a wff. @)
  lofeqwff $a wff ph = ps $.

  @( Outline of the proof of lofnono:

     <HTML><br></HTML>

     <HTML><ol>
     <li> ` ph = ph ` (lofid)</li>
     <li> ` ph = ph = [ ] ` (1 lofintr)</li>
     <li> ` ph = ph ps = [ ] ps ` (2 lofsub)</li>
     <li> ` [ ] ps = [ ] ` (lofc3)</li>
     <li> ` ph = ph ps = [ ] ` (3,4 loftrans)</li>
     <li> ` ph = ph ps ` (5 lofelim)</li>
     </ol></HTML>
     (Contributed by Naip Moro, 11-Mar-2017.) @)
  lofnono $p |- ph = ph ps $=
    ( lofeqwff df-lofjuxt df-lofvoid df-lofencl lofintr lofsub loftrans lofelim
    lofid lofc3 ) AACZBDZNEFZBDOMOBMAKGHBLIJ $.

  @( Derive a contradiction:  We prove false is equal to true by substituting
     the appropriate values into ~ lofnono .  (Contributed by Naip Moro,
     11-Mar-2017.) @)
  lofcontradiction $p |-  = [ ] $=
    ( df-lofvoid df-lofencl lofnono ) AABC $.
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                                 REFERENCES
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  1. [Spencer-Brown] Spencer-Brown, George, "Laws of Form", Allen & Unwin,
     London (1969).
$)

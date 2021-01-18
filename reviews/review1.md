# Summary

This paper defines a core language $\lambda^\forall_I$ (henceforth
lAI) which offers advanced reasoning (i.e., dependent types) with
proof-irrelevant implicit arguments and polymorphic subtyping (i.e.,
`forall a. a->a` is a subtype of `int->int`).

The feature interactions are complex. The system is, at core, a pure
type system (PTS), where types and terms form a single syntactic
category. Such systems typically have difficult metatheory, especially
when full dependency is allowed (as it is here). Adding subtyping is
yet another wrinkle. Implicit arguments---i.e., functions that need
not have their arguments specified---make things still more
difficult. Fixpoints further complicate things, since they introduce
the risk of nontermination (resolved by forcing explicit uses of
congruence, like in Sjöberg et al.'s Zombie).

The paper first shows that the system is internally consistent and has
transitive subtyping (a challenge in itself, requiring use of "unified
subtyping" from recent work by one of this paper's authors, along with
an explicit proof in terms of evaluation, rather than the typical
proof by elaboration). They go on to show that the system is sound
with respect to the classical rules for polymorphic subtyping from
Odersky and Läufer (i.e., every OL judgment can be translated to a
judgment in this system, by way of Dunfield and Krishnaswami's
system).

This paper doesn't discuss the practical aspects of their system at
all: there is no algorithmic formulation and, so, no usable
implementation. All of the metatheory has been formalized in Coq.

# Analysis

I like this work; it presents complex theories cleanly, building on a
variety of recent of advances in subtyping and its metatheory. There
are a few things I'd like to see happen:

 - Clearer explanation of how lAI relates to other work.

 - Clearer indication up front that implicits are necessarily proof
   irrelevant, and some concrete examples of programs your regime
   _disallows_.

 - A stronger conclusion. Rather than just summarizing the ideas and
   listing future work, can you give a broader outlook? Supposing you
   had an algorithmic system... what would you be able to do now?

One more thing that would help characterize the system but might be
too much:

  - Are there well formed types that are uninhabited? The monotype
    restriction on fixpoints may mean that diverging inhabitants can't
    be found at every type. The question of empty types seems
    important---on several occasions, the definitions and metatheory
    are forced to change because we don't know how to find inhabitants
    for arbitrary types. If there _were_ empty types, these
    metatheoretical concerns would be well justified. But if all types
    are inhabited, perhaps the theory can be made a touch simpler!

## Related work

There are many closely related systems that share features with lAI,
though it seems none share exactly lAI's features. It would be a
service to the field---and to your readers---to draw up a feature
table comparing the features lAI shares (and does not share) with a
variety of systems. In particular:

  - ICC
  - ICC*
  - GHC (and, in particular, comparison w/recent 'levity' work)
  - Agda
  - PITS
  - Yang and Oliveira's unified system [25]
  - Zombie (and maybe other related systems)

I'm not certain exactly what the features of this table might be, but
I can suggest:

  - Dependency
  - Subtyping
  - Implicits
  - Kind restrictions
  - Monotype restrictions
  - Algorithmic formulation (and if so, how sound/complete?)

The related work section omits two significant areas of inquiry:
refinement type systems like F* and Liquid Haskell, and Amin's DOT
theory.

Refinement type systems typically have both dependency and subtyping
(though there are some issues, e.g.,
<https://github.com/FStarLang/FStar/issues/65>). If you'd like to
compare to core calculi rather than systems/implementations, maybe
take a look at FH, which is the core calculus for Liquid Haskell (Belo
et al., ESOP 2011). Belo et al. is related for a less fortunate
reason---their reduction substitution lemma was wrong for reasons
similar to those mentioned on p26L56, highlighting how critical this
property is (Sekiyama et al., TOPLAS 2017 corrects the calculus but
doesn't include subtyping). Finally, FH does things the opposite way
of most systems: it defines subtyping post facto and shows that it's a
semantically safe (if syntactically ill typed) optimization.

I also expected to see discussion of DOT (Rompf and Amin, OOPSLA 2016)
and some of its followup work (e.g., "DOT with Implicit Functions"
from Jeffery, Scala Symposium 2019).

## Proof irrelevance

I only realized quite late in the paper that implicits had to be proof
irrelevant (p12L50-53). I have no qualms with this restriction---ICC
makes it at as well---but it is a heavy one! Coq, for example, makes
no such restriction on its implicits.

p13L27 Why doesn't an implicit lambda just erase to its body? I was so
confused I went and checked the Coq code, thinking the paper had a
typo. It doesn't---I must have an 'understand-o'. But... what am I
missing?  There's some invariant or idea in the system that I haven't
gotten.

p14L50-57 I struggled with this paragraph. Can lAI handle vectors of
implicit length, i.e., `Λn:Nat. λx:Vec n. ...`? A concrete example
would really help here.

p16L12-20 This paragraph is quite technical, but the gist of it should
show up much earlier in the paper.

p24L40 When you say "Implicit abstractions do not occur in type
computation due to the kind restriction of universal types", it would
be great to give an example of the kind of program that's
forbidden... such an example would go a long way towards making it
clear what your system can and can't handle!

p24L56 I didn't understand this lemma. Shouldn't it be the case that
`castdown N` has type `(\x:box. x) *`, and doesn't that type have kind
`box`, and doesn't it reduce? What am I missing? (I'm sure it's me,
and I just wonder what needs to be said to clear up my
confusion. Sadly, stepping through the Coq proofs didn't help me.)

## Syntax, naming, and notation

p7L17 We haven't yet seen the grammar, so the reader isn't yet
equipped to know what counts as a poly- or mono-type in your system
(or that the distinction matters, depending on their familiarity with
polymorphic subtyping and/or implicits!).

p9L55 We still haven't seen the grammar... I had to flip forward at
this point to be able to know which direction the definition was going
in! Relatedly, the use of the word "binder" here to refer to the
forall was somewhat confusing.

p10L15 It took quite some time to understand that mono-expressions
exclude implicit foralls but not explicit pis... and allow _either_
kind of lambda. I'm still a bit fuzzy on it, to be honest: a
mono-expression can _have_ a type with implicits, but it can't _be_
one? Right? More clarity here would be very helpful! Some kind of
discussion should also go in "Implicit Polymorphism" on p11L24-38.

p10L42 I'm not sure `Castup` and `Castdn` are the best possible names
here. Why not just write $\mathsf{expand}$ and $\mathsf{reduce}$ for
the terms (or `exp` and `red`)? These would be better rule names,
too. The discussion here should perhaps cite Zombie.

p11L14 I'm not sure a 'mostly' adopted convention is worth
mentioning. When _don't_ you do that?

p12L20 If `Castdn` triggers only one step, why does the outer cast
form remain in `R-Castdn`?

p14L20 Maybe call out the three non-structural rules (`S-Forall-L`,
`S-Forall-R`, `S-Sub`)? The appearance of `S-Forall` to resolve some
issues (p17L51) seems to indicate that "structurality" is an important
property!

p14L36 Maybe highlight the new kinding premises?

p16L21-25 I assumed the highlighted parts were important when I first
read the figure, and I was surprised to see they were in fact
redundant. I can imagine several useful highlights here: important
kinding premises, premises added due to the issues in Section 4.1.1,
places where mono-expressions are required, the three non-structural
rules, and redundant premises. I'd put them in that order of
importance. Maybe you can draw some `\fbox`en with various forms of
dashing, or use colors, or something?

p26L24-28 It'd be good to mark some turnstiles with a DK or
something---it wasn't immediately obvious that the first turnstile was
Dunfield and Krishnaswami's model of Oderskey and Läufer, and the
second was your judgment.

p26L30-43 I didn't understand these paragraphs at all.

p28L37-38 "However, we still face..." didn't make any sense to me.

It would be good to emphasize up front that pi and forall are
different---the former explicitly takes an argument and the latter is
implicit. I don't believe this is ever actually said in the paper!
Calling out the difference between `S-Pi` and `S-Forall` would be a
key move (p15).

## Coq proofs

It would be great to relate each theorem in the paper to its name in
Coq and the file its proven in---I had to dig around a bit.

p18L20-23 These lemmas have identical proof scripts. Why can't you
prove it in one go? (You'd have to generalize your fancy tactic...)

p18L49 The substitution theorem here was quite surprising: only
monotypes? Looking back at the rules, it's obvious: argument positions
demand monotypes anyway, so this property is enough for the
system. The text here, though, is confusing: its not _substitution_
that "imposes a mono-expression restriction", but rather, the type
system itself.

p20L49 The proof of generalized transitivity seems to go by _strong_
induction (i.e., due to the <= on the measures). Might be good to
mention this in the paper.

p21L11 Might be good to mention that Γ |- τ : A here.

p21L34 At the comment about sizes of expressions I immediately
wondered why you needed the derivation measure, too---and then saw it
a minute later below. Maybe mention up front which cases call for
which measures?

p22L31-33 The Coq proofs of these progress theorems are more
general. Maybe a short paragraph explaining the generality would be
helpful?

p23L39 I was surprised that the proof of subtype preservation is able
to find the valid instantiation (necessarily constructively). I can't
see the moment where that's happening in the custom tactics for the
Coq proof, though. Some more intuition here would be nice.

## Other comments

p6L13 Maybe say earlier that `MkF` is constructing typeclass
dictionaries? It's clear by the end of the page, but it will be easier
for readers to know it up front. I would also explicitly mention that
typeclass instantiation---a form of implicit argument in Haskell!---is
out of scope here, due to proof irrelevance.

p7L51 When you say "first attempt", it would be nice to give a clue as
to what goes wrong... we find out later that the answer is
'metatheory'. Can you give a short indication that this is the case?
Relatedly, are these rules admissible in the final system?

p8L32 Can you explain how Hindley-Milner relates to the ICC rules
(i.e., INST at variables and GEN at `let`s)?

p17L18 You should indicate up front that this "possible
generalization" is incorrect!

p17L29 This premise `Γ,x:A |- B : *` just gives us what we would have
tried to get by inversion... right?

p17L43 The core issue here is that the type A may be bottom, i.e.,
uninhabited... right?

p29L54 GHC has type families, which certainly _feel_ like type-level
lambdas. What do you mean here?

## Trivia

Can you alphabetize your bibliography? The natbib package makes this
easy.

Some of the papers in the bibliography are miscapitalized, e.g.,
"System fc" in [15]. Many citations are uneven: some just say POPL
(e.g., [16]), while others say "ACM SIGPLAN-SIGACT Symposium on
Principles of Programming Languages". I don't have a strong feeling
about which is better, but I think consistency is nice here.

Your Coq development works just fine on 8.12.0 (nice work, considering
your heavy automation!), though your install instructions are missing
the coq-ott package (and the omega tactic is deprecated in favor of
lia---a mere warning).

p2L35 "arizes" typo

p8L46 "subsumption rule of [the] typing relation"

p15 Figure 5 is too tall.

p18L54 "take [the] following"

p20L10 "head [a] Π type preserve[s] its kind"

p22L13 "by employ designs to make" isn't quite grammatical

p26L40 "to an open term" -> "on an open term"

p26L44 "inside [a] cast operator"

p26L50 "is a need" -> "would be a need"

p27L16 "we do not really polymorphic kinds" missing word?

p27L18 "then this complicates" -> "it would complicate"

p27L50 "Such [a] restriction"

p27L52 missing space before citation

p28L16-19 run-on sentence

p28L23 "Π type[s]"

p28L36 "problem here stay at first-order" agreement; probably drop the hyphen

p28L40 "We consider coming up with" where/when? do you mean it's future work?

p29L9 "While since we" extra word?

p29L18 missing space before citation

p30L25 I'm not certain "hot topic" is the best choice of words here.

p31L12 "eliminates [the] typing relation"

# Recommendations

I recommend some minor revisions. In particular:

  - Clarify up front that implicit arguments are proof
    irrelevant---perhaps even in the title! Given the various kinding
    and occurrence restrictions, what programs do you disallow?

  - A feature table comparing related systems.

  - A stronger conclusion, with more outlook for practice and/or
    application. What can we _do_ now (or when we have an algorithmic
    version of your system)?

  - Consider proving whether or not all types are inhabited.

Summary of the submission:
The paper presents a calculus supporting polymorphic subtyping and dependent types, and with explicit casts rather than a conversion rule. The main challenge is, indeed, to adapt polymorphic subtyping to dependent types, and the main idea is to use the approach of "unified subtyping", that is, to have a unique judgment for both typing and subtyping. Some important properties of the calculus are proved, and such proofs are mechanized in Coq.

Analysis of the submission:
The paper deals with an important issue (integration of subtyping and dependent types), and I find the idea of unified subtyping very good and coherent with the fact that dependent types unify, in a sense, terms and types. For what I am able to check the technical treatment is sound and sophisticated, moroever there are mechanized proofs and the authors make an effort in explaining the difficulties of the proofs.
Unfortunately I only have a medium expertise on the topic, so my understanding of the formalism is rather "syntactic", that is, I cannot deeply judge/appreciate all details. Also, also I cannot judge as an expert of the field the relevance with respect to previous work, which however seems significant to me.

The paper is very technical, and in my opinion the authors could make more effort in trying to make it understandable for a wider audience.

Recommendation:
I recommend to accept the paper with minor revision. My suggestions are mainly intended to add clarifications for a non-expert reader.

Detailed comments:

For what I understand, the idea of unified subtyping has been the main novelty of reference [25], and also casts where already introduced there. Here the main novelty is the integration with polymorphism, however a more detailed comparison with [25] would be useful, also in technical aspects such as choices in the syntax, etc. Also, I had a look at [25] and some aspects (e.g, the role of casts in avoiding to have to compute type equality) are explained much bettere there, perhaps you could import some of these explanations.

page 2 41-42 Here it is not clear which is the relation between strong normalization and explicit casts. Could you explain how explicit casts solve the problem? (see comment above, this is explained in [25])

17 at this point it is not clear what you mean by "conversion rule"

page 5 the example of indexed lists is not completely clear. Is the n:N parameter the initial index of the list? if it is the case can you say this? because the role of indexes is never shown
29 I do not understand the role of the "r" parameter in the definition of List, can you explain?
Please use a uniform font for code everywhere. For instance, map at line 34 is different from map at
line 35.
line 52: However, you do not show the definition of map

page 6: In the Functor example, it took me a lot of time to understand what is going on since you do not provide some simple explanation on Haskell-like syntax which I did not remember. It would be enough to recall that at line 13 Functor is defined by a record type, fmap is the name of the field selector, and field selection is written as application of the field selector.
It will also be useful to point out exactly what could not be expressed in, e.g., Haskell.
You say (line 33) that F is implicitly instantiated, but F is not Functor Id here?

page 7 you should explain which is the role of the type variables in Gamma; that is, what is only allowed if the type variable is available in Gamma

page 10 line 50: should reference [42] be [41]? (that is, [25])
Figure 2: you should at least mention the meaning of the "box" kind

page 12: perhaps you should justify better why upcasts are values

Figure 4: to use E both as metavariable and as index of the relation is a very bad choice (I was confused at the beginning)

page 17 line 34 you use "fresh in A" to mean "not occurring in A", right?

page 20 line 56 motivated by -> you mean "similar to"?

page 24 line 18: which is the "inner" downcast?

page 27 line 40: is it the first time that you mention principal type, perhaps should be defined

Typos and minor comments

page 2 31-32 repetition: ... a single level of syntax ... using the same syntax

page 3 9 it results on -> it results in ?

page 5 line 25 ommitted -> omitted
page 6 line 38: and instead -> and, instead
callcc example: again, please use a different font for code

page 7 50 can be can be -> can be

page 8
20 us -> our (?)
polymorphism on dependent type language -> something is missing?

page 11 line 10 similar syntax -> similar
line 40: two full stops

page 12 line 37 unfol -> unfold

page 14 line 47 the -> these

page 17 line 56 form -> from

page 19 line 19 break -> breaks

page 22 line 22 the sense -> in the sense

page 23 line 30 a -> an
45 preserves the type of expression -> preserve the type of expressions

page 26 line 22 terms type -> terms of type

page 27 line 15 "we do not really" should be removed
line 20 that, there -> that there
line 57 the the -> the

page 28 line 23 \Pi type -> \Pi types
line 31 depedent -> dependent
satisfy -> satisfies
Rule rule -> rule
stay -> stays
Moreover -> Moreover,

page 29 line 52 that, -> that

page 30 line 28 work of -> work on
enforce -> enforces

page 31 line 42 of polymorphic -> on polymorphic

References

 [1] American Matematical Society
 [14] Guru
 [15] System FC
 [20], [35], [55] Haskell

  [25] and [41] are the same

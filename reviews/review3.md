Summary of the submission:

Many functional languages provide a kind of polymorphic subtyping, where the system can automatically infer instatiations for the type paramters of a polymorphic function when it is invoked.  Recently, dependently-typed languages are becoming more prominent, e.g. to facilitate theorem proving in languages like Coq.  This paper extends the idea of polymorphic subtyping to a dependently-typed calculus.  The paper starts with motivating examples and an overview of the design.  The formalization of the calculus is then given, and the metatheory described.  The paper closes with a discussion of design issues and challenges, along with related work.

Analysis of the submission:

This paper addresses a real problem, I think.  Polymorphic subtyping is genuinely useful in functional languages and supporting dependent types with it could definitely be an advance.

The actual argument for the approach, though, wasn't great.  The indexed lists example seems super weird--it appears that indexes increase as the list goes on?  But I would expect the index to be the size of the list, and thus to decrease.  Consing onto a list won't work once you get to zero, which kind of defeats the purpose...or perhaps I'm not understanding something.

I also didn't understand the encoding technique in the list/map example.  What is r in the encoding of List?  Is this from Yang and Oliveira?

The functor example didn't do anything for me.  I expected this to mean functors in ML, but it wasn't.  I guess Haskell people will get it, but the example will be obscure for anyone not fully initiated into typed functional programming.

Anyway, despite the issues I had with following some of the examples, I do buy the basic value of doing this, and I got the gist of the list/map and callcc exmaples.  The informal presentation of the calculus was also good.

The formal presentation was mostly good, too--though there were some presentation issues.  I've seen the use of * (ground types) as a kind but not \box.  The paper cited the Calculus of Constructions, but I looked up [10] and didn't see a \box kind in that paper.  Please explain or give a reference.

I was also pretty lost on all discussion of mono-expressions.  I would like to understand more concretely the motivation for mono-expressions--it was discussed, but an example would help.  Also, how much of a expressiveness limitation is this?  I'm a bit surprised that you allow higher-rank polymorphism but can't instantiate type variables with polymorphic types; this seems inconsistent, at least philosophically, but perhaps I'm not understanding something.  Again a discussion would help.

The metatheory generally seemed sensible.  I can't be completely confident of my evaluation given some of the lack of understanding above, but the high-level reasoning makes sense, and of course it is supported by an automatically checked proof.

My biggest concern is the algorithmics of the system.  I understand this is a big challenge and the authors want to stage their work and leave that for another paper.  But to me it seems hopeless.  I know the Krishnaswami and Dunfield result was very difficult to obtain; at first glance this looks *much* harder.  And without automation, I can't see this system doing anyone any good; after all, the whole point of polymorphic subtyping is exactly so that type parameters can be automatically inferred.  So there's a gaping whole here--the approach is motivated mostly by practical concerns, but it isn't close to practical until the algorithmic issues are solved.  I do think the theory alone has some interest, though; so this is not a fatal flaw, but it is something that decreases my enthusiasm considerably.


Detailed comments:
 - abstract: arizing -> arising; later arize -> arise (unless this is a British spelling? but I don't think so, it seems "arize" is an obsolete form)
 - p 27 "the the"


Recommendations:

There's a problem here that is of substantial practical interest, but only if more work on the algorithmics is done.  The problem is also a nice bit of theory, but probably targeting a fairly narrow audience, at least until algorithmic supplements meets the theory that has been done (and it is unclear to me whether the algorithmics will ever work out).  The paper presentation is OK but there is definitely room for improvement.

I think after a revision, the paper could meet the bar for publication.  Revisions could improve the presentation quite a bit, but there is not an enormous amount of work involved (unless the authors can do the algorithmics--but that's more than I'd ask for in a major revision).  I'm not sure I'm likely to be super excited about it, given the missing algorithmics, but on the other hand it is valuable to publish preliminary work if it opens the door to follow-on work that could one day have substantial influence.  I just wish I had more confidence that there will be something beyond that door.  Hopefully the authors have more confidence than me, I presume that is why they are doing this work :)

So my recommendation would be to revise, but I'm not confident or enthusiastic about that judgment.  I think the paper should be sent back for revisions only if there is also support for that from other reviewers, otherwise it should be rejected.


References used in this review:

I only mention references cited in the submitted paper.


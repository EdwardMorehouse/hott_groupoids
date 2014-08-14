# HoTT Groupoids #

This is a small development to explore formalization of
[Homotopy Type Theory](http://homotopytypetheory.org/) in
[Agda](http://wiki.portal.chalmers.se/agda/pmwiki.php).
I started it in order to formalize some exercises from the
[HoTT book](http://homotopytypetheory.org/book/) and
[Robert Harper's course](http://www.cs.cmu.edu/~rwh/courses/hott/) at CMU.

This library differs from
[the standard one](https://github.com/HoTT/HoTT-Agda)
in that it uses the Martin-Löf eliminator (J) rather than Agda's pattern matching facility for paths, and it is based on the (higher) groupoid structure of types.
The former attibute is pedagogical and makes the library well-suited for formalizing the constructions in the HoTT book.
The latter attribute is experimental, but so-far seems promising as a way to structure proofs about paths primarily using combinators, thus reducing the need for complicated and ad-hoc λ-terms.
This structure is intended to:

- be more topological and categorical in flavor
- reduce code-on-code dependencies
- (eventually) facilitate the use of decision procedures and proof search strategies

Currently, the library contains combinators for only 2-dimensional groupoid structure.
But there is no reason that higher-dimensional structure could not be defined,
should the need arise.  The library depends on the
[Agda standard library](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary)
for some common, non-HoTT things, some of which are renamed in the Interlude.


This material is based upon work supported by the National Science Foundation under Grant Number 1116703.
Any opinions, findings, and conclusions or recommendations expressed in this material are those of the author(s) and do not necessarily reflect the views of the National Science Foundation.

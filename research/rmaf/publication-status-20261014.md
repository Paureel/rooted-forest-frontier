# Publication status of the base-two claim

This is a bounded source-status clarification, not a completed literature
review or a judgment that the thesis theorem is false.

- Mestel, Chaplick, Kelk and Meuwese, *Split-or-decompose: Improved FPT
  branching algorithms for maximum agreement forests*, arXiv v2 dated
  21 March 2026, introduction footnote 1, calls Whidden's thesis advancement
  unpublished. The paper gives the rooted bound O*(2.3391^k).
  Source: https://arxiv.org/html/2409.18634v2
- Whidden, Zeh and Beiko, *Supertrees Based on the Subtree Prune-and-Regraft
  Distance*, Systematic Biology 63(4), 566–581 (2014), describes edge protection
  in Methods. Figure 4 explicitly labels its new algorithm 2^k n. Thus the
  claim did appear in a journal article. The caption is not itself a proof of
  the worst-case runtime. This inspection does not claim to have audited the
  complete supplementary material.
  Source: https://academic.oup.com/sysbio/article/63/4/566/2848417
  DOI: https://doi.org/10.1093/sysbio/syu023
- The author's rSPR README separately lists *Computing the SPR Distance of
  Binary Rooted Trees in O(2^k n) Time* as In Preparation, 2013. The README
  could be stale; it is evidence about the listed manuscript, not proof that
  no later publication exists.
  Source: https://github.com/cwhidden/rspr

The thesis itself is a public source containing correctness and runtime
arguments in Chapter 6, not merely an announcement:
https://dalspace.library.dal.ca/bitstreams/3b246ff4-5ec2-452f-95ab-ef1aed255373/download

Inference: the 2026 comparison appears to distinguish publication of a
complete complexity proof from publication of the method or its claimed
bound. No separate full-proof publication or public refutation was located
in the bounded searches in this chat. The sources do not establish why a
planned manuscript did not appear. Our local proof-gap findings are new
audit observations, not an identified historical refutation; they do not
disprove O(2^k n).

Accordingly, novelty remains open. A correct thesis proof would count
mathematically, and a base between 2 and 2.3391 cannot be called a new best
bound without resolving that prior claim and the root convention.

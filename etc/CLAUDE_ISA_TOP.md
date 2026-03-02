# Rules for  Formalizing top1.tex statements (no proofs) in Isabelle/HOL


- You should assume that everything in Isabelle Complex_Main is available
This includes a lot of math already- don't repeat those!


## No Duplication and Extra Content
- There may be no duplicates of the statements from Complex_Main 
- There may be no lemmas/theorems that do not have a counterpart in top1.tex . Everything has to be clearly marked with the top1.tex counterpart.

## Work Strategy
- Your task is to formalize **all** definitions and statements in top1.tex, **no proofs** yet (everything admitted but no axioms).
- Everything from top1.tex has to have before it a clear comment about its origin in top1.tex like this (you must also add the line number in top1.tex):
(** from §48 Lemma 48.1 (direction): open-set Baire implies closed-set Baire **)
(** LATEX VERSION: Lemma 48.1: X is Baire iff countable intersections of dense open sets are dense. **)
- Do this in the top1.tex order, page by page, chapter by chapter, patiently, in smaller batches. It can take the whole day. Quality is critical, speed is not.
- You can create extra definitions as needed/suitable for smooth formulation of everything in top1.tex .
- Always double-check everything you did.
- Keep carefully fixing any incorrect/bad definitions/theorems you find (note that this may lead to fixing some more things, etc).
- You **ARE** supposed to do it all, i.e. also the complex substiantial infrastructure work required. We really need **ALL** definitions    
  and theorems from the top1.tex file stated exactly as they should. No slacking, no excuses, no stubs, no
  highly redundant reports: work hard for hours/days (and let others worry about the token limits).
- Frequently lookup the necessary notions defined before the Top1 section. Those should be
  completely trusted and built upon.
- Also, always lookup all current Definitions and Theorems in the Complex_Main before creating a new one. Be sure to remove/avoid duplicities.
- Do not introduce axioms that are exactly the same as the theorems you want to prove - it only duplicates and pollutes. In general, try to avoid adding axioms - it's better to have admitted theorems that will be (hopefully) eventually proved.
- Strongly prioritize properly finishing/debugging all proper definitions and (stating/proving) theorems from *all* sections of top1.tex . Doing the exercises is not as time-critical (although it may be occasionally needed as a prerequisite and generally useful, so use your judgement).
- Again: No "infrastructure lemmas" that are not in top1.tex . Only the stuff from top1.tex . Nothing more, nothing less . Perfectly stated, double-checked and debugged.





## Isabelle Language Details

### Logic System
- **This is classical Isabelle/HOL** (not constructive)
- everybody know that, right?



## Definition Quality Standards                                                                                                                  
 
  ### ✅ DEFINITIONS must be SUBSTANTIVE 
  - Definitions must capture actual mathematical content 
  - **NEVER create stub definitions that just return `True`** 
  - If you cannot make a definition substantive, DO NOT add it
  - instead, start gradually defining the needed concepts so that you can add the definition after some work
 
  ### Good vs Bad Definitions 
 
  
  When they are NOT acceptable: 
 
  - Predicates that just return True without capturing the concept 
  - Definitions that provide no mathematical content 
  - Any definition where True appears as the main body
  - simplified or a stub
 
  "No proofs yet" applies to THEOREMS, not DEFINITIONS: 
 
  - ✅ Theorems: State correctly, use sorry. for proof 
  - ❌ Definitions: Must be substantive and perfect, no simplifications. 
  - The distinction: Theorems make claims (no proof). Definitions establish meaning (must be meaningful). 
 
  Review and Cleanup Required 
 

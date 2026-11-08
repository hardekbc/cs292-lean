# Course Project Logistics
## Single-person or groups of two

- No more than two people

- Group projects must be scoped appropriately, i.e., I expect a group to accomplish more than a single person

## Due dates

- 11/03: Project proposal
- 11/19: Mid-project report
- 12/11: Final project report

## Proposal

A document (in PDF or plain-text format) describing:

- What you will be formalizing exactly

  - Should be concrete, i.e., not a vague concept but a very specific goal

  - Should be detailed enough that even if I don't know anything about the topic, I can understand what you'll be doing (e.g., if you're formalizing a distributed computing protocol then describe the protocol in detail)

- What properties you will be proving about that formalization

  - Again, be concrete; you don't need to have the exact formal statements that you'll be proving, but you should have the informal prose versions of those statements

### Scoping the project

I will try to determine if the projects are properly scoped (i.e., not too hard
but not too easy), but this will be difficult...expect that we may have to make
adjustments along the way.

- If it's too hard, talk to me about it and we can try to come up with various ways to make it easier

- If it's too easy, it's still in your interest to talk to me about it: if I see the final version and I think it's too trivial, that will be reflected in your grade

Try to come up with something that can be staged, starting with something
relatively easy (along the lines of the lecture examples and exercises) and then
adding complexity. Explain the stages in your proposal.

## Mid-project report

This report is mainly a way to (1) check on your progress, and (2) give you a
chance to modify the proposed project based on what you've discovered so far.

You will submit:

- The Lean code you have developed so far

- A document (in PDF or plain-text format) reflecting on what you've accomplished, what you still need to accomplish, any difficulties you've encountered that have slowed your progress, whether you think the project proposal needs to be modified, and if so how

## Final project report

You will submit:

- The Lean code you have developed

- A document (in PDF or plain-text format) reflecting on what you've accomplished, what you were not able to accomplish, what difficulties prevented you from accomplishing everything you wanted, and how you might do things differently if you were starting the project afresh and/or how you might extend the project if you had more time

# Course Project Ideas

Here is a non-comprehensive list of possible projects; feel free to propose
ideas that are not listed here. Be sure to do an online search, both generally
and specifically in Mathlib, to be sure that there isn't any already-existing
work that subsumes your proposal.

- Verified functional algorithms and data structures (e.g., from the book "Functional Data Structures and Algorithms"). Note that there some examples of such things in Lean already, and I'll want to see something other than those.

- A verified compiler from some source language (starting from an AST) to an IR and then to assembly. The source language can be something simple of your own design (gradually extended with more features to add complexity).

- Theory of computation: formalizing and proving various properties of context-free languages, Turing machines, etc

- Verified parsing (LL-k recursive descent, parser combinators, etc)

- Type soundness for various advanced typing features (parametric and subtype polymorphism, linearity +borrowing, etc)

- Verified distributed/concurrent computing protocols (dining philosophers, byzantine generals, etc)

- Crypto, e.g., implementing a logic of belief (e.g., BAN logic) and using it to verify authentication protocols

- Verified compression algorithms

- Verified graph algorithms

- Verified HW design, e.g., RISC-V processor

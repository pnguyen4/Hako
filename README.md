# Hako
CS225 Final Project

## Submission

### Project Summary

Our initial starting code primarily drew from homeworks 5-8 for functions &
closures, mutable state, classes and objects, and type safety. 

By the end of the project timeline, we have implemented while loops, conditional
expressions (LT, GT, EQ), single and multiple inheritance with associated logic
to handle keywords `this` and `super`, security labels (binary security
lattice) & security types, join and meet functions on labels, type checker
enforces non-interference to guarantee confidentiality as well as basic type
safety for all expressions (including OO, mutation, and loops). Many new tests
to ensure correctness for interpreter and type checker were written, as well as
a demonstration of information flow. 

Efforts not reflected in the code is the work put into researching proper
implementations for inheritance models, type checkers, and defining the proper
semantics for the program, most of which are listed in the SEMANTICS.md file.

### Challenges

One of the challenges in writing the program for multiple inheritance was
effectively whittling down the argument list for initializing an object and its
parents without increasing code complexity. There were varying models for
inheritance that differ between languages in addition to the logic for dynamic
dispatching and use of the `super` keyword. In deciding which models of
inheritance that we wanted to implement into the language, we opted to choose
the most intuitive and based it off of existing languages with guidance of some
research papers.

Something that was harder than anticipated was coming up with an implementation
of the language that handled security in a way that kept program writing
practical (and non verbose) whilst also staying true to the formal model of
non-interference while also limiting complexity in the haskell code wherever
possible. This was most apparent with the class declarations, which motivated
the current design of OO typing. 

### Learning

In researching inheritance, we came about mathematical definitions of
inheritance and associated behavior. A generalized inheritance scheme was
proposed which was difficult to implement, so those routes were avoided for a
more intuitive approach to multiple inheritance.

While writing the information flow demo we learned a lot about how I/O monads
work in haskell. Reading the recommended papers from Volpano-Smith-Irvine and
Heintze-Riecke (as well as doing my own research and talking in office hours)
gave us a deeper look at information flow security than was covered in CS295B.

### References

* Cook, W. (1989). A denotational semantics of inheritance.<br>
  https://www.cs.utexas.edu/~wcook/papers/thesis/cook89.pdf
* Volpano, D., Smith, G., & Irvine, C. (2009). A sound type system for secure
  flow analysis.<br>
  http://users.cis.fiu.edu/~smithg/papers/jcs96.pdf
* Heintz, N. & Riecke, J. G. (2003). The SLam calculus: programming with
  secrecy and integrity.<br>
  https://www.cs.cornell.edu/andru/cs711/2003fa/reading/heintze98slam.pdf

---

## Checkpoint 2

Accomplishments:

While Loops were the first thing that was implemented after handing in
checkpoint 1.  Basic conditional expressions were also added to fully leverage
control flow expressions.  The type handling for integer and boolean
expressions was updated for correctness and clarity and the type checker now
also handles Var, Let, App, Box, Unbox, Assign, While, New, GetField, SetField,
and Call expressions.  Our object oriented code now features inheritance with
full support of hierarchical and multiple inheritance.  Many tests and helper
functions were written in the process of developing these features.

Future Plans:

Code cleanup and stability will be the main focus going forward.  A brief
tester function meant to demonstrate and/or check for interferance is in the
works.

---

## Checkpoint 1

Accomplishments:

Combining elements of previous homework assignments, we have implemented an
interpreter that handles objects, boxes, first class functions, closures,
stores, and environments.  We have also added security labels to basic types
(with a binary security lattice in mind: secret vs public) in order to create
security types.  Join and Meet helper functions were written to determine the
security level of data.  The type environment and type checker was extended to
handle security types.  Int, Bool, Box, and Function expressions were updated
to require security level declarations at creation.

Future Plans:

Immediate priorities are expanding the type checker to handle more expressions
and incorporate it into the interpreter to return errors on type mismatch.  A
‘securitycheck’ function to check programs for information flow
non-interference to enforce confidentiality of secret data is in the works.
While loops and inheritance are also being worked on.

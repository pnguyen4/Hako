# Hako
CS225 Final Project
Checkpoint 2

Current Accomplishments:

While Loops were the first thing that was implemented after handing in checkpoint 1.
Basic conditional expressions were also added to fully leverage control flow expressions.
The type handling for integer and boolean expressions was updated for correctness and clarity and the type checker now also handles Var, Let, App, Box, Unbox, Assign, While, New, GetField, SetField, and Call expressions.
Our object oriented code now features inheritance with full support of hierarchical and multiple inheritance.
Many tests and helper functions were written in the process of developing these features.

Future Plans:

Code cleanup and stability will be the main focus going forward.
A brief tester function meant to demonstrate and/or check for interferance is in the works.

================================================================================

Checkpoint 1 Accomplishments:

Combining elements of previous homework assignments, we have implemented an interpreter that handles objects, boxes, first class functions, closures, stores, and environments.
We have also added security labels to basic types (with a binary security lattice in mind: secret vs public) in order to create security types.
Join and Meet helper functions were written to determine the security level of data.
The type environment and type checker was extended to handle security types.
Int, Bool, Box, and Function expressions were updated to require security level declarations at creation.

Checkpoint 1 Future Plans:

Immediate priorities are expanding the type checker to handle more expressions and incorporate it into the interpreter to return errors on type mismatch.
A ‘securitycheck’ function to check programs for information flow non-interference to enforce confidentiality of secret data is in the works.
While loops and inheritance are also being worked on.

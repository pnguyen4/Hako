# Hako
CS225 Final Project

Current Accomplishments:

Combining elements of previous homework assignments, we have implemented an interpreter that handles objects, boxes, first class functions, closures, stores, and environments. We have also added security labels to basic types (with a binary security lattice in mind: secret vs public) in order to create security types. Join and Meet helper functions were written to determine the security level of data. The type environment and type checker was extended to handle security types. Int, Bool, Box, and Function expressions were updated to require security level declarations at creation.

Future Plans:

Immediate priorities are expanding the type checker to handle more expressions and incorporate it into the interpreter to return errors on type mismatch. A ‘securitycheck’ function to check programs for information flow non-interference to enforce confidentiality of secret data is in the works. While loops and inheritance are also being worked on.

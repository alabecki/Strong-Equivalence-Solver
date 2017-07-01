SE Models Solver

1. Introduction:

The program reads text files with logic programs. When reading a file with only one logic program, it will return the set of strong equivlance (SE) models for that program. When reading a file with two logic programs it will return the SE models for each program and indicate whether or not the two programs are equivalent or if one program entails the other.

2. Program File Format:

Each rule has the following format:
  a :- b

Where "a" is a disjunction of atomic propositions and "b" is a set of propositional formulas with negation as failure instead of classical negation.

The following symbols may be used for Boolean connectives:

{"&", "*", ","} for AND
{"|", "+", ";"} for OR 
{"->", "=>"} for IMPLIES

In addition to Boolean connectives we have:
{"~", "!", "not"} for NOT (negation as failure)
{"TRUE", "1"} for TRUE
{"FALSE", 0} for FALSE



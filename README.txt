_________________________________________________________________________
SE Models Solver
_________________________________________________________________________ 
 
1. Installation
To run the program, a computer must have Python 3.x installed. The program 
was written on Python 3.6 but may run correctly on older versions. Version 
3.4 or higher, however, is recommended. The program can be opened in on the 
command-line in Windows or Linux machines. 

In the command line, go to the directory in which you have placed the 
folder containing the program and type:

	python se_main.py

(If you have Anaconda installed on your computer you need only type 
“z_main.py”)

The program makes use of the logic module from the sympy library. It is 
recommended that the user employ pip when installing Python libraries. To 
install sympy simply type:

       pip install sympy	(perhaps with a “sudo”)


If you have both Python 2.x and 3.x installed on your system, it might 
run Python 2.x by default, which will cause trouble both when trying to 
run the program and when installing modules. 

If this is the case, type the following into the command prompt: 
	
	alias python='/usr/bin/python3'   (Linex)
	
	alias python='python3'		  (Mac)

Then install sympy as follows:
	
	python3.x -m pip install sympy

This second way of installing sympy may be necessary even if you already
have python 3 active.

If you have trouble installing through pip, please try using Easy Install:

	easy_install sympy		(perhaps with sudo prefixed)

This second way of installing sympy may be necessary even if you already
have python 3 active.

If none of these methods of installing sympy work see:

http://docs.sympy.org/latest/install.html

_________________________________________________________________________

2. Introduction:

The program reads text files with logic programs. When reading a file with
only one logic program, it will return the set of strong equivalence (SE)
models for that program. The algorithm used to determine the SE of a program
was first presented in F. Lin (2002) and H. Turner (2003).When reading a 
file with two logic programs, it will return the SE models for each program
and indicate whether or not the two programs are equivalent or if one program
entails the other.

_________________________________________________________________________

3. Program File Format:

Each rule has the following format:
	a :- b
	or
	a ::= b

Where "a" is a disjunction of atomic propositions and "b" is a set of 
propositional formulas with negation as failure instead of classical negation.

The following symbols may be used for Boolean connectives:

{"&", "*", ","} for AND
{"|", "+", ";"} for OR 
{"->", "=>"} for IMPLIES

In addition to Boolean connectives, there is:
{"~", "!", "not"} for NOT (negation as failure)
{"TRUE", "1"} for TRUE
{"FALSE", "0"} for FALSE

Members of b are separated with periods "." (although, one can just as 
easily make b a single conjunctive formula)

It is necessary to have a line with "SECOND" between the two programs 
so that the program knows where the first programs ends and where the second begins.

All lines not including rules should begin with #

Examples:

	p :- 
	q :- TRUE
	p;q ::= not r
	p;r :- r,s
	p|q :- s -> r
	q ::=  not(p * q)
 	:- q & r

_________________________________________________________________________

4. Functions

After opening the program the user will be prompted to enter the name of a 
program file. There are two choices here depending on whether the file contains
one or two programs. 

Upon receiving a single program file, the program will return the set of SE 
models for that program.
Upon receiving a double program file, the program will return the SE models
of both programs and tell the user how the two are related. The programs may
be strongly equivalent or one might entail the other, or no such relations might
obtain. 

The user then has one of three additional choices:

(a) Print the results to a .txt file
(b) Add a rule to a loaded program and view the models of the resulting program
(c) Remove a rule from a loaded program and view the models of the resulting program 


_________________________________________________________________________

References


Hudson Turner. 2003. Strong equivalence made easy: nested expressions and weight
constraints. Theory Pract. Log. Program. 3, 4 (July 2003), 609-622. 

Lin, F. 2002. Reducing strong equivalence of logic programs to entailment in
classical logic. In Proc. of KR’02. 170–176.

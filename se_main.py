

from sympy import Symbol
from sympy.abc import*
from sympy.logic.boolalg import to_cnf
from sympy.logic.boolalg import Not, And, Or
from sympy.logic.inference import satisfiable, valid
from mpmath import*
from itertools import product
import sys
from copy import deepcopy
from shutil import copyfile
from itertools import*
import os
import re
from sympy import simplify

from se_classes import*
from se_functions import*


commands = {
	"1": "Get SE models of a logic program (from file with one program)",
	"2": "Check if logic program  A entails logic program B (from file with two programs)",
	"3": "Exit"
}

	
#Main_____________________________________________________________________________________________________________________
print("\n \n")
print ("=================================================================================== ")
print("____________________________________________________________________________________\n")
print("--------------- Weclome to the Strong Equivalence Solver ---------------------------")
print("_____________________________________________________________________________________ \n")
print ("==================================================================================== \n")


FALSE = Symbol("FALSE")
TRUE = Symbol("TRUE")

while(True):
	do = ""
	while do not in commands.keys():
		for k, v in commands.items():
			print("%s: %s" % (k, v))
		do = input()
	if(do == "3"):
		sys.exit()
	if(do == "1"):
		res = get_file()
		file = res[0]
		file_name = res[1]
		file.seek(0)
		model = initializeA(file)
		print("\n")
		print("----------------------------------------------------------------------------------")
		print("Models")
		print("----------------------------------------------------------------------------------")
		for m in model:
			print("< %s, %s >" % (m.X, m.Y))
		print("\n")
		file.close()

	elif(do == "2"):
		res = get_file()
		file = res[0]
		file_name = res[1]
		file.seek(0)
		line_num = 0
		modelA = initializeA(file)
		modelB = initializeB(file)
		print("\n")
		print("----------------------------------------------------------------------------------")
		print(" A Models:")
		print("----------------------------------------------------------------------------------")
		for m in modelA:
			print("< %s, %s >" % (m.X, m.Y))
		print("\n")
		print("----------------------------------------------------------------------------------")
		print(" B Models:")
		print("----------------------------------------------------------------------------------")
		for m in modelB:
			print("< %s, %s >" % (m.X, m.Y))
		print("\n")

		se_modelA = get_se_model(modelA)
		se_modelB = get_se_model(modelB)


		if se_modelA == se_modelB:
			print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
			print("The the programs are Strongly Equivalant")
			print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")

		elif se_modelB.issubset(se_modelA):
			print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
			print("The second program entails the first")
			print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
		elif se_modelA.issubset(se_modelB):
			print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
			print("The first program entails the second")
			print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
		
		else:
			print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
			print("The programs are not Strongly Equivalant and it is not the case that one entails the other")
			print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")

		file.close()
		print("\n")

	elif(do == "3"):
		print("Goodby")

	else:
		print("I'm sorry, could you repeat your command? \n")



	









	#print("Lets see what just happened_________________________________________________________________________")


#Now#for k, v in rules.items():
	#	print("%s, %s " % (k, v.item))
	#	print("Head: %s" % (v.head))
	#	print("P-Body: ")
	#	for p in v.pos_body:
	#		print (p)
	#	print ("N-Body: ")
	#	for p in v.neg_body:
	#		print(p) that we have the rules of the program P stored, we need to construct gamma(P).



	


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
	"1": "Open file containing a single program to get SE models",
	"2": "Open file containing two programs to get SE models and check for equilvance",
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
		propositions = obtain_atomic_formulas(file)
		file.seek(0)
		rules = construct_programA(file)		# parses input text, make a Rule object for each rule, saves objects in dictionary
		file.seek(0)
		print("number of rules: %s" % len(rules))
		print("Rules: ")
		for r in rules.values():
			print (r.name, r.item)
		formulas = formula_translation(rules)
		print("formulas______________________________________________________:")
		for f in formulas:
			print(f)
		crules = rule_compliment(rules, propositions)
		print("_____ crules:")
		for crule in crules:
			print(crule)
		_rules = construct_programA(crules)
		print("_________ _rules:")
		for rule in _rules.values():
			print(rule.item)
		_formulas= formula_translation(_rules)
		print("_formulas____________________________________________________")
		for _f in _formulas:
			print (_f)
		print("comIorg:")
		comIorg = get_com_org_imp(propositions)
		for cio in comIorg:
			print(cio)
		condition = create_condition(formulas, _formulas, comIorg)
		print("Condition:")
		print(condition)
		print("YY:")
		YY = satisfiable(condition, all_models = True)
		listYY = list(YY)
		print("listYY:")
		for l in listYY:
			print(l)
		print("Models")
		model = get_Models(listYY)
		for m in model:
			print ("X: %s" % (m.X))
			print("Y: %s " % (m.Y))
		file.close()

	elif(do == "2"):
		res = get_file()
		file = res[0]
		file_name = res[1]
		file.seek(0)
		line_num = 0
		propositions = obtain_atomic_formulas(file)
		print("Propositions:")
		for p in propositions:
			print(p)
		file.seek(0)
		rules1 = construct_programA(file)
		print("number of rules in Program A: %s" % len(rules1))
		print("Program A Rules: ")
		for r in rules1.values():
			print(r.name, r.item)
		file.seek(0)
		rules2 = construct_programB(file)
		print("number of rules in Program B: %s" % len(rules2))
		print("Program B Rules: ")
		for r in rules2.values():
			print(r.name, r.item)
		formulas1 = formula_translation(rules1)
		print("formulas A ______________________________________________________:")
		for f in formulas1:
			print(f)
		formulas2 = formula_translation(rules2)
		print("formulas B ______________________________________________________:")
		for f in formulas2:
			print(f)
		crules1 = rule_compliment(rules1, propositions)
		print("_____ crules A:")
		for crule in crules1:
			print(crule)
		crules2 = rule_compliment(rules2, propositions)
		print("_____ crules B:")
		for crule in crules2:
			print(crule)
		_rules1 = construct_programA(crules1)
		print("_________ _rules A:")
		for rule in _rules1.values():
			print(rule.name, rule.item)
		crules2.insert(0, "SECOND")
		_rules2 = construct_programB(crules2)
		print("_________ _rules B:")
		for rule in _rules2.values():
			print(rule.name, rule.item)
			print("Head %s, pb: %s, nb: %s" % (rule.head, rule.pos_body, rule.neg_body))
		_formulas1= formula_translation(_rules1)
		print("_formulas A ____________________________________________________")
		for _f in _formulas1:
			print (_f)
		_formulas2= formula_translation(_rules2)
		print("_formulas B____________________________________________________")
		for _f in _formulas2:
			print (_f)
		print("comIorg:")
		comIorg = get_com_org_imp(propositions)
		for cio in comIorg:
			print(cio)
		
		condition1 = create_condition(formulas1, _formulas1, comIorg)
		print("Condition A:")
		print(condition1)
		print("YY:")
		condition2 = create_condition(formulas2, _formulas2, comIorg)
		print("Condition B:")
		print(condition2)
		print("YY:")
		YY1 = satisfiable(condition1, all_models = True)
		listYY1 = list(YY1)
		print("listYY A:")
		for l in listYY1:
			print(l)
		YY2 = satisfiable(condition2, all_models = True)
		listYY2 = list(YY2)
		print("listYY B:")
		for l in listYY2:
			print(l)
		print("A Models")
		model1 = get_Models(listYY1)
		for m in model1:
			print ("X: %s" % (m.X))
			print("Y: %s " % (m.Y))
		print("B Models")
		model2 = get_Models(listYY2)
		for m in model2:
			print ("X: %s" % (m.X))
			print("Y: %s " % (m.Y))

		se_model1 = get_se_model(model1)
		se_model2 = get_se_model(model2)

		if se_model2 == se_model1:
			print("The the programs are Strongly Equivalant")
		else:
			print("The programs are not Strongly Equivalant")

		file.close()





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



	
# SE Lin

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



def gamma1_rules(rules, propositions):
	print("Gamma 1 rules ______________________________________________________")
	crules = []
	for r, rule in rules.items():
		new = ""
		_temp = str(rule.item)
		temp = re.sub(r'\s+', '', _temp)
		temp = temp.strip('')
		for p in propositions:
			print("temp before: %s" % (temp))
			if "not"+ str(p) in temp:
				print("Do we get here?")
				temp = temp.replace("not" + str(p), "not_" + str(p))
				print("temp after %s" % (temp))  
		crules.append(temp)
	return crules
		

def gamma2_rules(rules, propositions):
	print("Gamma 2 rules ______________________________________________________________")
	crules = []
	for r, rule in rules.items():
		new = ""
		_temp = str(rule.item)
		temp = re.sub(r'\s+', '', _temp)
		temp = temp.strip('')
		for p in propositions:
			if str(p).startswith("_"):
				continue
			else:
				ex = "_" + str(p)
				temp = temp.replace(str(p), ex)
		crules.append(temp)
	return crules

def get_comp_imp(propositions):
	comIorg = []
	for p in propositions:
		if "_" not in str(p):
			temp = "~"+ str(p) + "|" + "_" + str(p)
			for char in temp:
				char = Symbol(temp)
			temp = simplify(temp)
			comIorg.append(temp)
	return comIorg


def get_Models(listYY):
	models = []
	count = 0
	if len(listYY) == 1 and listYY[0] == False:
		return models
	else:
		for state in listYY:
			y = set()
			x = set()
			xy = set()
			for key, value in state.items():
				if value == True and "_" not in str(key):
					x.add(key)
			for key, value in state.items():
				if "_" not in str(key):
					temp = "_" + str(key)
					temp = Symbol(temp)
					if state[temp] == True:
						y.add(key)

			pair = (frozenset(x),frozenset(y))
			xy.add(pair)
			name = "m" + str(count)
			new = Model(name, y, x, xy)
			models.append(new)
			count += 1
		return models


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
			print (r.name, r.item, r.head, r.pos_body, r.neg_body)

		g1 = gamma1_rules(rules, propositions)

		g2 = gamma2_rules(rules, propositions)


		g1rules = construct_programA(g1)
		g2rules = construct_programA(g2)

		gamma1 = formula_translation(g1rules)
		gamma2 = formula_translation(g2rules)

		print("g1 formulas:__________________________")
		for g in gamma1:
			print (g)
		print("g1 formulas:___________________________")
		for g in gamma2:
			print(g)

		print("comp_imp:")
		comp_imp = get_comp_imp(propositions)
		for ci in comp_imp:
			print(ci)

		condition = create_condition(gamma1, gamma2, comp_imp)
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
		
	elif(do == "2"):
		res = get_file()
		file = res[0]
		file_name = res[1]
		file.seek(0)
		propositions = obtain_atomic_formulas(file)
		file.seek(0)
		rulesA = construct_programA(file)		# parses input text, make a Rule object for each rule, saves objects in dictionary
		file.seek(0)
		print("number of rules: %s" % len(rulesA))
		print("Rules: ")
		for r in rulesA.values():
			print (r.name, r.item, r.head, r.pos_body, r.neg_body)


		g1A = gamma1_rules(rulesA, propositions)

		g2A = gamma2_rules(rulesA, propositions)


		g1rulesA = construct_programA(g1A)
		g2rulesA = construct_programA(g2A)

		print("g2rulesA______________________________________________________")
		for r in rulesA.values():
			print (r.name, r.item, r.head, r.pos_body, r.neg_body)


		gamma1A = formula_translation(g1rulesA)
		gamma2A = formula_translation(g2rulesA)

		print("Gamma 1A formulas____________________")
		for g in gamma1A:
			print(g)
		print("Gamma 2A formulas ____________________")
		for g in gamma2A:
			print(g)

		print("comp_imp:")
		comp_imp = get_comp_imp(propositions)
		for ci in comp_imp:
			print(ci)

		conditionA = create_condition(gamma1A, gamma2A, comp_imp)
		print("Condition:")
		print(conditionA)
		print("YY:")
		YYA = satisfiable(conditionA, all_models = True)
		listYYA = list(YYA)
		print("listYY:")
		for l in listYYA:
			print(l)
		

		file.seek(0)
		rulesB = construct_programB(file)		# parses input text, make a Rule object for each rule, saves objects in dictionary
		file.seek(0)
		print("number of rules: %s" % len(rulesB))
		print("Rules: ")
		for r in rulesB.values():
			print (r.name, r.item)

		g1B = gamma1_rules(rulesB, propositions)

		g2B = gamma2_rules(rulesB, propositions)

		g1B.insert(0, "SECOND")
		g2B.insert(0, "SECOND")

		g1rulesB = construct_programA(g1B)
		g2rulesB = construct_programA(g2B)

		print("g2rulesB______________________________________________________")
		for v in g2rulesB.values():
			print(v.item)

		gamma1B = formula_translation(g1rulesB)
		gamma2B = formula_translation(g2rulesB)

		print("Gamma 1B formulas____________________")
		for g in gamma1B:
			print(g)
		print("Gamma 2B formulas ____________________")
		for g in gamma2B:
			print(g)

		conditionB = create_condition(gamma1B, gamma2B, comp_imp)
		print("Condition:")
		print(conditionB)
		print("YY:")
		YYB = satisfiable(conditionB, all_models = True)
		listYYB = list(YYB)
		print("listYY:")
		for l in listYYB:
			print(l)
		
		print("A Models")
		modelA = get_Models(listYYA)
		for m in modelA:
			print ("X: %s" % (m.X))
			print("Y: %s " % (m.Y))

		print("B Models")
		modelB = get_Models(listYYB)
		for m in modelB:
			print ("X: %s" % (m.X))
			print("Y: %s " % (m.Y))


		se_modelA = get_se_model(modelA)
		se_modelB = get_se_model(modelB)

		if se_modelA == se_modelB:
			print("The the programs are Strongly Equivalant")
		else:
			print("The programs are not Strongly Equivalant")





	else:
		print("I'm sorry, could you repeat your command? \n")




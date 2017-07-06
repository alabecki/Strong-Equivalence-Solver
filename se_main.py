

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
#from win32 import win32print



commands = {
	"1": "Get SE models of a logic program (from file with one program)",
	"2": "Check if logic program  A entails logic program B (from file with two programs)",
	"3": "Exit"
}

additionA = {
	"1": "Write models to .txt",
	"2": "Add rule to program and regenerate SE Models",
	"3": "Remove rule from program and regenerate SE Models",
	"4": "Return to Primary Commands"
}

additionB = {
	"1": "Write models to .txt",
	"2": "Add rule to program A and regenerate SE Models",
	"3": "Add rule to program B and regenerate SE Models",
	"4": "Remove rule from program A and regenerate SE Models",
	"5": "Remove rule from program B and regenerate SE Models",
	"6": "Return to Primary Commands"
}

	
#Main_____________________________________________________________________________________________________________________
print("\n \n")
print ("=================================================================================== ")
print("____________________________________________________________________________________\n")
print("--------------- Welcome to the Strong Equivalence Solver ---------------------------")
print("_____________________________________________________________________________________ \n")
print ("==================================================================================== \n")


FALSE = Symbol("FALSE")
TRUE = Symbol("TRUE")

while(True):
	do = ""
	while do not in commands.keys():
		for k, v in commands.items():
			print("%s: %s" % (k, v))
		print("\n")
		do = input()
	if(do == "3"):
		sys.exit()
	if(do == "1"):
		res = get_file()
		file = res[0]
		file_name = res[1]
		file.seek(0)
		propositions = obtain_atomic_formulas(file, "A")
		file.seek(0)
		rules = construct_program(file, "A")		# parses input text, make a Rule object for each rule, saves objects in dictionary
		file.seek(0)
		#print("number of rules: %s" % len(rules))
		print("Program rules: ")
		for r in rules.values():
			print (r.name, r.item)
		model = initialize(rules, propositions, "A")
		print("\n")
		print("----------------------------------------------------------------------------------")
		print("Models")
		print("----------------------------------------------------------------------------------")
		for m in model:
			print("< %s, %s >" % (m.X, m.Y))
		print("\n")
		file.close()

		more = True
		while more == True:
			print("Would you like to do anything else with this program?---------------------------")
			for k, p in additionA.items():
				print("%s: %s" % (k, p))
			print("\n")
			opt = ""
			while (opt not in additionA.keys()):
				opt = input()
			if opt == "1":
				save = create_txt_single(model)
				#print(save)
			if opt == "2":
				print("Please enter a new rule to add to the Program")
				new_rule = input()
				#_file = open(res[1], "a+")
				add_rule(new_rule, rules)
				print("Program Rules:")
				for rule in rules.values():
					print (rule.item)
				print("\n")
				add_proposition(new_rule, propositions)
				#augment_programA(new_rule, res[1])
				print("The %s has been added to the program" % (new_rule))
				print("Push 'enter' to get the new models:")
				input()
				#file = open(res[1], "r")
				model = initialize(rules, propositions, "A")
				for m in model:
					print("< %s, %s >" % (m.X, m.Y))
				print("\n")

			if opt == "3":
				print("Which of the following rules would you like to remove from the Program?")
				for k, v in rules.items():
					print(v.item)
				drop = input()
				drop = re.sub(r'\s+', '', drop)	
				drop = drop.strip()
				flag = False
				dummy = deepcopy(rules)
				for d, dum in dummy.items():
					comp = re.sub(r'\s+', '', dum.item)
					comp = comp.strip()
					if drop == comp:
						#key = get_rule_name_from_item(drop, rules)
						#print("key: %s" % (key))
						#rules.pop(key)
						rules.pop(d)
						print("%s has been removed from the program\n" % (drop))
						print("Program Rules:")
						for k, v in rules.items():
							print(v.item)
						print("Push 'enter' to get the new models:")
						input()
						#file = open(res[1], "r")
						model = initialize(rules, propositions, "A")
						for m in model:
							print("< %s, %s >" % (m.X, m.Y))
							flag = True
				if flag == False:
					print("%s is not one of the rules in the program" % (drop))

			if opt == "4":
				more = False	


	elif(do == "2"):
		res = get_file()
		file = res[0]
		file_name = res[1]
		file.seek(0)
		propositions = obtain_atomic_formulas(file, "A")
		file.seek(0)
		rulesA = construct_program(file, "A")		# parses input text, make a Rule object for each rule, saves objects in dictionary
		file.seek(0)
		#print("number of rules: %s" % len(rules))
		print("Program A rules: ")
		for r in rulesA.values():
			print (r.name, r.item)
		file.seek(0)
		propositions = obtain_atomic_formulas(file, "B")
		print("propositions B")
		for p in propositions:
			print(propositions)
		file.seek(0)
		rulesB = construct_program(file, "B")		# parses input text, make a Rule object for each rule, saves objects in dictionary
		file.seek(0)
		#print("number of rules: %s" % len(rules))
		print("Program B rules: ")
		for r in rulesB.values():
			print (r.name, r.item)

		modelA = initialize(rulesA, propositions, "A")
		modelB = initialize(rulesB, propositions, "B")

		results(modelA, modelB)

		file.close()

		more = True
		while more == True:
			print("Would you like to do anything else with these programs?-------------------------")
			for k, p in additionB.items():
				print("%s: %s" % (k, p))
			print("\n")
			opt = ""
			while (opt not in additionB.keys()):
				opt = input()
			if opt == "1":
				save = create_txt_double(modelA, modelB)
				#print_models(save)
			if opt == "2":
				print("Please enter a new rule to add to Program A")
				new_rule = input()
				#_file = open(res[1], "a+")
				add_rule(new_rule, rulesA)
				print("Program A Rules:")
				for rule in rulesA.values():
					print (rule.item)
				print("\n")
				add_proposition(new_rule, propositions)
				#augment_programA(new_rule, res[1])
				print("The %s has been added to program A" % (new_rule))
				print("Push 'enter' to get the new models:")
				input()
				#file = open(res[1], "r")
				modelA = initialize(rulesA, propositions, "A")
				modelB = initialize(rulesB, propositions, "B")
				results(modelA, modelB)
			if opt == "3":
				print("Please enter a new rule to add to Program B")
				new_rule = input()
				#_file = open(res[1], "a+")
				add_rule(new_rule, rulesB)
				print("Program B Rules:")
				for rule in rulesB.values():
					print (rule.item)
				print("\n")
				add_proposition(new_rule, propositions)
				#augment_programA(new_rule, res[1])
				print("The %s has been added to program B" % (new_rule))
				print("Push 'enter' to get the new models:")
				input()
				#file = open(res[1], "r")
				modelA = initialize(rulesA, propositions, "A")
				modelB = initialize(rulesB, propositions, "B")
				results(modelA, modelB)

				#add_rule(new_rule, rules)

			if opt == "4":
				print("Which of the following rules would you like to remove from Program A?")
				for k, v in rulesA.items():
					print(v.item)
				drop = input()
				drop = re.sub(r'\s+', '', drop)	
				drop = drop.strip()
				flag = False
				dummy = deepcopy(rulesA)
				for d, dum in dummy.items():
					comp = re.sub(r'\s+', '', dum.item)
					comp = comp.strip()
					if drop == comp:
						rulesA.pop(d)
						#key = get_rule_name_from_item(drop, rulesA)
						#print("key: %s" % (key))
						#rulesA.pop(key)
						print("%s has been removed from program A\n" % (drop))
						print("Program A Rules:")
						for k, v in rulesA.items():
							print(v.item)
						print("Push 'enter' to get the new models:")
						input()
						#file = open(res[1], "r")
						modelA = initialize(rulesA, propositions, "A")
						modelB = initialize(rulesB, propositions, "B")
						results(modelA, modelB)
						flag = True
				if flag == False:
					print("%s is not one of the rules in program A" % (drop))

			if opt == "5":
				print("Which of the following rules would you like to remove from Program B?")
				for k, v in rulesB.items():
					print(v.item)
				drop = input()
				drop = re.sub(r'\s+', '', drop)	
				drop = drop.strip()
				dummy = deepcopy(rulesB)
				for d, dum in dummy.items():
					comp = re.sub(r'\s+', '', dum.item)
					comp = comp.strip()
					if drop == comp:
						rulesB.pop(d)
						#key = get_rule_name_from_item(drop, rulesB)
						#print("key: %s" % (key))
						#rulesB.pop(key)
						print("%s has been removed from program B\n" % (drop))
						print("Program B Rules:")
						for k, v in rulesB.items():
							print(v.item)
						print("Push 'enter' to get the new models:")
						input()
						#file = open(res[1], "r")
						modelA = initialize(rulesA, propositions, "A")
						modelB = initialize(rulesB, propositions, "B")
						results(modelA, modelB)
						flag = True
				if flag == False:
					print("%s is not one of the rules in program A" % (drop))

			if opt == "6":
				more = False	

	elif(do == "3"):
		print("\n")
		print("Goodbye \n")

	else:
		print("\n")
		print("I'm sorry, could you repeat your command? \n")



	







	
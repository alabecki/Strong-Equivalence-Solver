

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

	
def get_file():
	while True:
		file_name = input("Please input the name of a text-file containing a set of rules \n")
		file_name = file_name + ".txt"
		if(os.path.exists(file_name)):
			_file = open(file_name, "r+")
			print("Name of file: %s \n" % (file_name))
			res = [_file, file_name]
			return res
		else:
			print("The file you selected does not exist, please try again\n")

def obtain_atomic_formulas(file):
	propositions = set()
	lines = (line.rstrip() for line in file)
	lines = (line for line in lines if line)
	for line in lines:
		if line.startswith("#"):
			continue 
		_line = re.sub(r'\s+', '', line)
		_line = _line.replace(".", ",")
		_line = _line.replace("&", ",")
		_line = _line.replace("|", ",")
		_line = _line.replace("->", ",")
		_line = _line.replace("~", ",")
		_line =  _line.replace(":-", ",")
		_line = _line.replace("(", "")
		_line = _line.replace(")", "")
		_line = _line.replace("not", "")

		new_props = _line.split(",")
		new_props = list(filter(None, new_props))
		for prop in new_props: 
			new = Symbol(prop)
			_new = Symbol("_" + prop)
			propositions.add(new)
			propositions.add(_new)
	return propositions

def _mapping(propositions):
	mapping = {}
	for p in propositions:
		if "_" in str(p):
			continue
		else:
			corra = Symbol("_" + p)
			mapping[p] = corra
	return mapping


def construct_program(file):
	rules = {}
	count = 0
	lines = (line.rstrip() for line in file) # All lines including the blank ones
	lines = (line for line in lines if line)
	print("Lines")
	for line in lines:
		print(line)
		if line.startswith("#"):
			continue
		pos_body = []
		neg_body = []
		name = "r" + str(count)
		print("Line: %s" % (line))
		_line = re.sub(r'\s+', '', line)	
		_line = _line.strip()
		print("Stripped Line: %s" % (_line))
		if _line.startswith(":-"):
			print("Starts with :-")
			body = _line.replace(":-", "")
			if "." not in body:
				print("No . in body")
				if body.startswith("not"):
					print("starts with not")
					neg_body.append(body)
				else:
					print("does not start with not")
					pos_body.append(body)
				new = Rule(name, _line, "", pos_body, neg_body)
				rules.update({name: new})
				count += 1
			else:
				body = div[1].split(".")
				for b in body:
					if b.startswith("not"):
						print("States with 'not' ")
						neg_body.append(b)
					else:
						print("Does not start with 'not' ")
						pos_body.append(b)
				new = Rule(name, _line, "", pos_body, neg_body)
				rules.update({name: new})
				count += 1
		elif _line.endswith(":-"):
			print("Ends with :-")
			head = _line.replace(":-", "")
			new = Rule(name, _line, head, "", "")
			rules.update({name: new})
			count += 1

		else:
			print("Does not end with :-")
			#print("_Line: %s" % (_line))
			div = _line.split(":-")
			head = div[0]
			if "." not in div[1]:
				print("No . in body")
				if div[1].startswith("not"):
					print("starts with not")
					neg_body.append(div[1])
				else:
					print("does not start with not")
					print("WTF is div1[1]???? %s" % (div[1]))
					pos_body.append(div[1])
					name = "r" + str(count)
					new = Rule(name, line, head, pos_body, neg_body)
					rules.update({name: new})
					count += 1
			else:
			#print("div1[0]: %s" % (div1[0]))
			#print("div1[1]: %s" % (div1[1]))
				print("Has . in body")
				body = div1[1].split(".")
				for b in body:
					if b.startswith("not"):
						neg_body.append(b)
					else:
						pos_body.append(b)
				name = "r" + str(count)
				new = Rule(name, line, head, pos_body, neg_body)
				rules.update({name: new})
				count += 1
	return rules

def formula_translation(rules):
	formulas = []
	for r, rule in rules.items():
		pante = ""
		nante = ""
		if len(rule.pos_body) == 0 and len(rule.neg_body) == 0:
			con = rule.head
			for char in con:
				char = Symbol(char)
			con = simplify(con)
			formulas.append(con)
			continue
		if len(rule.pos_body) > 0:
			pante = str(rule.pos_body[0]).replace("not", "~")
			if "->" in str(rule.pos_body[0]):
				imp = str(rule.pos_body[0]).split("->")
				pante = "~" + imp[0] + "|" + imp[1]
			for char in pante:
				char = Symbol(char)
			pante = simplify(pante)
			if len(rule.pos_body) > 1:
				print("WTG is the len? %s" % (len(rule.pos_body)))
				count = 1
				while count <= len(rule.pos_body):
					add = str(rule.pos_body[count]).replace("not", "~")
					if "->" in str(rule.pos_body[count]):
						imp = str(rule.pos_body[count]).split("->")
						imp[0] =  "~" + imp[0]
						add = imp[0] + "|" + imp[1]
					for char in add:
						 char = Symbol(char)
					add = simplify(add)
					pante = And(add, pante)
					count += 1
		if len(rule.neg_body) > 0:
			nante = str(rule.neg_body[0]).replace("not", "~")
			if "->" in str(rule.neg_body[0]):
				imp = str(rule.neg_body[0]).split("->")
				pante = "~" + imp[0] + "|" + imp[1]
			for char in nante:
				char = Symbol(char)
			nante = simplify(nante)
			print(nante)
			if len(rule.neg_body) > 1:
				count = 1
				while count <= len(rule.neg_body):
					add = rule.neg_body[count].replace("not", "~")
					if "->" in str(rule.neg_body[count]):
						imp = str(rule.neg_body[count]).split("->")
						add = "~" + imp[0] + "|" + imp[1]
					for char in add:
						char = Symbol(char)
					add = simplify(nante)
					nante = And(add, nante)
					count += 1
		if pante and nante:		
			ante = And(pante, nante)
		else:
			if pante:
				ante = pante
			else:
				ante = nante
		print("before head check")
		if len(rule.head) > 0:
			print("after head check")
			con = rule.head
			for char in con:
				char = Symbol(con)
			con = simplify(rule.head)
		#print("Con: %s " %(con))
		#print("ante: %s "% (ante))
			print("Do we get here?")
			print(ante)
			ante = Not(ante)
			print(ante)
			f = Or(ante, con)
			formulas.append(f)
		else:
			print("Should be no head for second rule!")
			ant = Not(ante)
			formulas.append(ant)
	return formulas

def rule_compliment(rules, propositions):
	crules = []
	for r, rule in rules.items():
		new = ""
		temp = str(rule.item)
		for p in propositions:
			if str(p).startswith("_"):
				continue
			elif str(p) in temp:
				#print("Before %s " % (temp))
				ex = "_" + str(p)
				#print(ex)
				temp = temp.replace(str(p), ex)
				print("After1 *****************: %s" % (temp))
				temp = temp.replace("~" + ex, "~" + str(p))
				temp = temp.replace("not" + ex, "not" + str(p))
				#print("After2: %s" % (temp))
		crules.append(temp)
	return crules


def formula_compliment(formulas, propositions):
	_formulas = []
	for f in formulas:
		new = ""
		for p in propositions:
			temp = str(f)
			if str(p) in temp:
				ex = "_" + str(p)
				temp = temp.replace(str(p), ex)
				temp = temp.replace("~" + ex, "~" + str(p))
				new = Symbol(temp)
		_formulas.append(new)
	return _formulas


def construct_worlds(propositions):
	_op = []
	for p in propositions:
		_op.append(str(p))
	_op.sort()
	op = []
	for o in _op:
		new = Symbol(o)
		op.append(new)
	num_worlds = list(range(2**len(propositions)))	#calculates number of rows in the table from which the worlds will be obtained
	world_names = ["w" + str(i) for i in num_worlds]	#creates a unique name for each world: "w" plus an integer
	n = len(propositions)								#number of propositions for table creation
	table = list(product([False, True], repeat=n))		#creation of a truth table
	worlds = {}											#initiates an empty list of worlds
	count = 0
	for row in table:
		world = dict(zip(op, row))
		name = world_names[count]			#each state is a dictionary associating a truth value with each propositional
		worlds[name] = world							#the new world is added to the list of worlds
		count +=1
	return worlds

def get_com_org_imp(propositions):
	comIorg = []
	for p in propositions:
		if "_" not in str(p):
			temp = "~_"+ str(p) + "|" + str(p)
			for char in temp:
				char = Symbol(temp)
			temp = simplify(temp)
			comIorg.append(temp)
	return comIorg

def create_condition(formula, _formulas, comIorg):
	conditions = comIorg[0]
	for f in formulas:
		conditions = And(f, conditions)
	for _f in _formulas:
		conditions = And(_f, conditions)
	for cio in comIorg:
		conditions = And(cio, conditions)
	return conditions

def get_Models(listYY):
	models = []
	count = 0
	if len(listYY) == 1 and listYY[0] == False:
		return models
	else:
		for state in listYY:
			y = set()
			x = set()
			for key, value in state.items():
				if value == True and "_" not in str(key):
					y.add(key)
					temp = "_" + str(key)
					#for char in temp:
					#	char = Symbol(char)
					if state[temp] == True:
						x.add(key)
			name = "m" + count
			new = Model(name, y, x)
			models.append(new)
			count += 1
		return models 





#Main_____________________________________________________________________________________________________________________
print("\n \n")
print ("=================================================================================== ")
print("____________________________________________________________________________________\n")
print("--------------- Weclome to the Strong Equivalence Solver ---------------------------")
print("_____________________________________________________________________________________ \n")
print ("==================================================================================== \n")

while(True):
	do = ""
	print("What would you like to do? \n")
	while(do != "1" and do !="2"):
		do = input("(1) Open a file, (2), exit program\n")
	if(do == "2"):
		sys.exit()
	if(do == "1"):
		res = get_file()
		file = res[0]
		file_name = res[1]
	else:
		print("I'm sorry, could you repeat your command? \n")

	file.seek(0)
	propositions = obtain_atomic_formulas(file)
	for p in propositions:
		print(p)
	file.seek(0)
	rules = construct_program(file)		# parses input text, make a Rule object for each rule, saves objects in dictionary
	file.seek(0)
	print("number of rules: %s" % len(rules))
	print("Rules: ")
	for k, v in rules.items():
		print("%s, %s " % (k, v.item))
		print("Head: %s" % (v.head))
		print("P-Body: ")
		for p in v.pos_body:
			print (p)
		print ("N-Body: ")
		for p in v.neg_body:
			print(p)

	worlds = construct_worlds(propositions)

	formulas = formula_translation(rules)
	print("formulas______________________________________________________:")
	for f in formulas:
		print(f)

	crules = rule_compliment(rules, propositions)
	print("_____ crules:")
	for crule in crules:
		print(crule)

	_rules = construct_program(crules)

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

	#for yy in YY:
	#	print(yy)


	listYY = list(YY)
	print("listYY:")
	for l in listYY:
		print(l)
	print("Models")
	model = get_Models(listYY)

	for m in model:
		print (m.X)
		print(m.Y)









	#print("Lets see what just happened_________________________________________________________________________")


#Now that we have the rules of the program P stored, we need to construct gamma(P).



	
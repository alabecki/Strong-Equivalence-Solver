

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


commands = {
	"1": "Open file containing a single program to get SE models",
	"2": "Open file containing two programs to get SE models and check for equilvance",
	"3": "Exit"
}

	
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
	flag = False
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


def construct_programA(file):
	flag = False
	rules = {}
	count = 0
	lines = (line.rstrip() for line in file) # All lines including the blank ones
	lines = (line for line in lines if line)
	print("Lines")
	for line in lines:
		print(line)
		if "SECOND" in line:
			return rules
		if line.startswith("#"):
			continue
		pos_body = []
		neg_body = []
		name = "r" + str(count)
		_line = re.sub(r'\s+', '', line)	
		_line = _line.strip()
		if _line.startswith(":-"):
			print("Starts with :-")
			body = _line.replace(":-", "")
			if "." not in body:
				if body.startswith("not"):
					neg_body.append(body)
					new = Rule(name, _line, "", pos_body, neg_body)
					rules.update({name: new})
					count += 1
				else:
					pos_body.append(body)
					new = Rule(name, _line, "", pos_body, neg_body)
					rules.update({name: new})
					count += 1
			else:
				body = div[1].split(".")
				for b in body:
					if b.startswith("not"):
						neg_body.append(b)
					else:
						pos_body.append(b)
				new = Rule(name, _line, "", pos_body, neg_body)
				rules.update({name: new})
				count += 1
		elif _line.endswith(":-"):
			head = _line.replace(":-", "")
			new = Rule(name, _line, head, "", "")
			rules.update({name: new})
			count += 1

		else:
			#print("_Line: %s" % (_line))
			div = _line.split(":-")
			head = div[0]
			if "." not in div[1]:
				#print("No . in body")
				if div[1].startswith("not"):
				#	print("starts with not")
					neg_body.append(div[1])
				else:
				#	print("does not start with not")
				#	print("WTF is div1[1]???? %s" % (div[1]))
					pos_body.append(div[1])
				name = "r" + str(count)
				new = Rule(name, line, head, pos_body, neg_body)
				rules.update({name: new})
				count += 1
			else:
				#print("Has . in body")
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


def construct_programB(file):
	print("ProgramB")
	rules = {}
	count = 0
	flag = False
	lines = (line.rstrip() for line in file) # All lines including the blank ones
	lines = (line for line in lines if line)
	for line in lines:
		if "SECOND" in line:
			flag = True
		if flag == False:
			continue
		else:
			print("Begin--")
			if line.startswith("#"):
				continue
			pos_body = []
			neg_body = []
			name = "r" + str(count)
			_line = re.sub(r'\s+', '', line)	
			_line = _line.strip()
			if _line.startswith(":-"):
				print("Starts with :-")
				body = _line.replace(":-", "")
				if "." not in body:
					if body.startswith("not"):
						neg_body.append(body)
						new = Rule(name, _line, "", pos_body, neg_body)
						rules.update({name: new})
						count += 1
					else:
						pos_body.append(body)
						new = Rule(name, _line, "", pos_body, neg_body)
						rules.update({name: new})
						count += 1
				else:
					body = div[1].split(".")
					for b in body:
						if b.startswith("not"):
							neg_body.append(b)
						else:
							pos_body.append(b)
					new = Rule(name, _line, "", pos_body, neg_body)
					rules.update({name: new})
					count += 1
			elif _line.endswith(":-"):
				head = _line.replace(":-", "")
				new = Rule(name, _line, head, "", "")
				rules.update({name: new})
				count += 1

			else:
				print("_Line: %s" % (_line))
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
		_temp = str(rule.item)
		temp = re.sub(r'\s+', '', _temp)
		temp = temp.strip('')
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
				print("After2: %s" % (temp))
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

def create_condition(formulas, _formulas, comIorg):
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
			xy = set()
			for key, value in state.items():
				if value == True and "_" not in str(key):
					y.add(key)
					temp = "_" + str(key)
					#for char in temp:
				#	char = Symbol(char)
					temp = Symbol(temp)
					if state[temp] == True:
						x.add(key)
			pair = (frozenset(x),frozenset(y))
			xy.add(pair)
			name = "m" + str(count)
			new = Model(name, y, x, xy)
			models.append(new)
			count += 1
		return models

def get_se_model(model):
			se_model = set()
			for m in model:
				item = frozenset(m.XY)
				se_model.add(item)
			return se_model 


#Main_____________________________________________________________________________________________________________________
print("\n \n")
print ("=================================================================================== ")
print("____________________________________________________________________________________\n")
print("--------------- Weclome to the Strong Equivalence Solver ---------------------------")
print("_____________________________________________________________________________________ \n")
print ("==================================================================================== \n")

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

	elif(do == "2"):
		res = get_file()
		file = res[0]
		file_name = res[1]
		file.seek(0)
		line_num = 0
		propositions = obtain_atomic_formulas(file)
		print("Propositions B:")
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
		_rules2 = construct_programB(crules2)
		print("_________ _rules B:")
		for rule in _rules2.values():
			print(rule.name, rule.item)
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



	
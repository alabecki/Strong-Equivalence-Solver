# SE Functions

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

FALSE = Symbol("FALSE")
TRUE = Symbol("TRUE")

def initializeA(file):
		file.seek(0)
		propositions = obtain_atomic_formulas(file, "A")
		file.seek(0)
		rules = construct_programA(file)		# parses input text, make a Rule object for each rule, saves objects in dictionary
		file.seek(0)
		print("number of rules: %s" % len(rules))
		print("Program A rules: ")
		for r in rules.values():
			print (r.name, r.item)
		formulas = formula_translation(rules)
		print("Formulas __________________________________________________________")
		for f in formulas:
			print(f)
	
		crules = rule_compliment(rules, propositions)
		print("CRULES____________________________________________________________")
		for c in crules:
			print (c)
	
		_rules = construct_programA(crules)
	
		_formulas= formula_translation(_rules)
		
		comIorg = get_com_org_imp(propositions)
		condition = create_condition(formulas, _formulas, comIorg)
		print("condition______________________________________________________________")
		print(condition)
		YY = satisfiable(condition, all_models = True)
		listYY = list(YY)
		print("\n")
		model = get_Models(listYY)
		return model

def initializeB(file):
		file.seek(0)
		propositions = obtain_atomic_formulas(file, "B")
		file.seek(0)
		rules = construct_programB(file)
		file.seek(0)
		print("number of rules: %s" % len(rules))
		print("Program B rules: ")
		for r in rules.values():
			print (r.name, r.item)
		formulas = formula_translation(rules)
		print("Formulas __________________________________________________________")
		for f in formulas:
			print(f)
		crules = rule_compliment(rules, propositions)
		crules.insert(0, "SECOND")
		print("CRULES______________________________________________________________________-")
		for c in crules:
			print(c)
		_rules = construct_programB(crules)
		print("__rules))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
		for r in _rules.values():
			print (r.name, r.item)
		_formulas= formula_translation(_rules)
		print("________formulas______________________________________________________")
		for f in _formulas:
			print(f)
		comIorg = get_com_org_imp(propositions)
		condition = create_condition(formulas, _formulas, comIorg)
		print("condition______________________________________________________________")
		print(condition)
		YY = satisfiable(condition, all_models = True)
		listYY = list(YY)
		model = get_Models(listYY)
		return model


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

def obtain_atomic_formulas(file, X):
	propositions = set()
	lines = (line.rstrip() for line in file)
	lines = (line for line in lines if line)
	flag = False
	for line in lines:
		if X == "B":
			if "SECOND" in line:
				flag = True
			if flag == False:
				continue
		if X == "A":
			if "SECOND" in line:
				return propositions
		if line.startswith("#") or "SECOND" in line:
			continue 
		_line = re.sub(r'\s+', '', line)
		_line = _line.replace(".", ",")
		_line = _line.replace("&", ",")
		_line = _line.replace(";", ",")
		_line = _line.replace("->", ",")
		_line = _line.replace("=>", ",")
		_line = _line.replace("~", "")
		_line = _line.replace("!", "")
		_line =  _line.replace(":-", ",")
		_line = _line.replace("(", "")
		_line = _line.replace(")", "")
		_line = _line.replace("not", "")
		_line = _line.replace("TRUE", "")
		_line = _line.replace("FALSE", "")
		_line = _line.replace("+", ",")
		_line = _line.replace("*", ",")

		new_props = _line.split(",")
		new_props = list(filter(None, new_props))
		for prop in new_props: 
			new = Symbol(prop)
			#_new = Symbol("_" + prop)
			propositions.add(new)
			#propositions.add(_new)
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
	#print("Lines")
	for line in lines:

		if "SECOND" in line:
			return rules
		if line.startswith("#"):
			continue
		pos_body = []
		neg_body = []
		name = "r" + str(count)
		_line = re.sub(r'\s+', '', line)	
		_line = _line.strip()
		if _line.startswith(":-") or _line.startswith(str(FALSE)):
		#print("Starts with :-")
			head = ""
			if _line.startswith(str(FALSE)):
				head = "FALSE"
			body = _line.replace(":-", "")
			body = body.replace("FALSE", "")
			if "." not in body:
				if body.startswith("not"):
					neg_body.append(body)
					new = Rule(name, _line, "", pos_body, neg_body)
					rules.update({name: new})
					count += 1
				else:
					pos_body.append(body)
					new = Rule(name, _line, head, pos_body, neg_body)
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
		elif _line.endswith(":-") or _line.endswith(str(TRUE)):
			head = _line.replace(":-", "")
			head = head.replace("TRUE", "")
			pos_body = ""
			if _line.endswith(str(TRUE)):
				pos_body = "TRUE"
			new = Rule(name, _line, head, pos_body, "")
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
				body = div[1].split(".")
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
			print(line)
			if line.startswith("#") or "SECOND" in line:
				continue
			pos_body = []
			neg_body = []
			name = "r" + str(count)
			_line = re.sub(r'\s+', '', line)	
			_line = _line.strip()
			if _line.startswith(":-") or _line.startswith(str(FALSE)):
				print("Starts with :- or FALSE")
				head = ""
				if _line.startswith(str(FALSE)):
					head = "FALSE"
				body = _line.replace(":-", "")
				body = body.replace("FALSE", "")
				if "." not in body:
					if body.startswith("not"):
						neg_body.append(body)
						new = Rule(name, _line, head, pos_body, neg_body)
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
			elif _line.endswith(":-") or _line.endswith(str(TRUE)):
				head = _line.replace(":-", "")
				head = head.replace("TRUE", "")
				pos_body = ""
				if _line.endswith(str(TRUE)):
					pos_body = "TRUE"
				new = Rule(name, _line, head, pos_body, "")
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
						pos_body.append(div[1])
					print("DO WE GET HERE?????????????")
					print(line)
					print(neg_body)
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
		if (len(rule.pos_body) == 0 and len(rule.neg_body) == 0) or rule.pos_body == "TRUE":
			con = rule.head
			con = con.replace(";", "|")
			con = con.replace("+", "|")
			for char in con:
				char = Symbol(char)
			con = simplify(con)
			formulas.append(con)
			continue
		if len(rule.pos_body) > 0:
			pante = str(rule.pos_body[0]).replace("not", "~")
			pante = pante.replace("!", "~")
			pante = pante.replace(";", "|")
			pante = pante.replace("+", "|")
			pante = pante.replace(",", "&")
			pante = pante.replace("*", "&")
			if "->" in str(rule.pos_body[0]):
				imp = str(rule.pos_body[0]).split("->")
				pante = "~" + imp[0] + "|" + imp[1]
			if "=>" in str(rule.pos_body[0]):
				imp = str(rule.pos_body[0]).split("=>")
				pante = "~" + imp[0] + "|" + imp[1]
			for char in pante:
				char = Symbol(char)
			print(pante)
			pante = simplify(pante)
			if len(rule.pos_body) > 1:
				print("WTG is the len? %s" % (len(rule.pos_body)))
				count = 1
				while count < len(rule.pos_body):
					print(count)
					add = str(rule.pos_body[count]).replace("not", "~")
					add = add.replace("!", "~")
					add = add.replace(";", "|")
					add = add.replace("+", "|")
					add = add.replace(",", "&")
					add = add.replace("*", "&")
					if "->" in add:
						imp = add.split("->")
						imp[0] =  "~" + imp[0]
						add = imp[0] + "|" + imp[1]
					if "=>" in add:
						imp = add.split("=>")
						imp[0] =  "~" + imp[0]
						add = imp[0] + "|" + imp[1]
					for char in add:
						 char = Symbol(char)
					add = simplify(add)
					pante = And(add, pante)
					count += 1
		if len(rule.neg_body) > 0:
			nante = str(rule.neg_body[0]).replace("not", "~")
			nante = nante.replace("!", "~")
			nante = nante.replace(";", "|")
			nante = nante.replace("+", "|")
			nante = nante.replace(",", "&")
			nante = nante.replace("*", "&")
			if "->" in nante:
				imp = nante.split("->")
				nante = "~" + imp[0] + "|" + imp[1]
			if "=>" in nante:
				imp = nante.split("=>")
				nante = "~" + imp[0] + "|" + imp[1]
			for char in nante:
				char = Symbol(char)
			nante = simplify(nante)
			#print(nante)
			if len(rule.neg_body) > 1:
				count = 1
				while count < len(rule.neg_body):
					add = str(rule.neg_body[count]).replace("not", "~")
					add = add.replace("!", "~")
					add = add.replace(";", "|")
					add = add.replace("+", "|")
					add = add.replace(",", "&")
					add = add.replace("*", "&")
					if "->" in add:
						imp = add.split("->")
						add = "~" + imp[0] + "|" + imp[1]
					if "=>" in nante:
						imp = nante.split("=>")
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
	#	print("before head check")
		if len(rule.head) > 0 and rule.head != "FALSE" and rule.head != "0":
	#		print("after head check")
			con = rule.head
			con = con.replace(";", "|")
			con = con.replace("+", "|")
			for char in con:
				char = Symbol(con)
			con = simplify(con)
		#print("Con: %s " %(con))
		#print("ante: %s "% (ante))
	#		print(ante)
			ante = Not(ante)
	#		print(ante)
			f = Or(ante, con)
			formulas.append(f)
		else:
	#		print("**********************************************************************")
			ant = Not(ante)
			#print(ante)
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
				print("Before %s " % (temp))
				ex = "_" + str(p)
				print(ex)
				temp = temp.replace(str(p), ex)
				print("After1 *****************: %s" % (temp))
				temp = temp.replace("~" + ex, "~" + str(p))
				temp = temp.replace("not" + ex, "not" + str(p))
				temp = temp.replace("!" + ex, "!" + str(p))
				print("After2: %s" % (temp))
		crules.append(temp)
	return crules


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



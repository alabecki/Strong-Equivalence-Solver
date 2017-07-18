# SE Functions
#Windows Version 

from sympy import Symbol
from sympy.abc import*
from sympy.logic.boolalg import to_cnf
from sympy.logic.boolalg import Not, And, Or
from sympy.logic.inference import satisfiable, valid
from mpmath import*
from itertools import product
from copy import deepcopy
from shutil import copyfile
from itertools import*
import re
from sympy import simplify
import os, sys 
#from pywin32 import win32print 
#from win32 import win32print


from se_classes import*

second = "SECOND"

def initialize(rules, propositions, pro):   # Calls a sequence of functions that calculate the SE models 
		formulas = formula_translation(rules)
		#print("Formulas __________________________________________________________")
		#for f in formulas:
		#	print(f)
		crules = rule_compliment(rules, propositions)
		_rules = construct_program(crules, "A")
		_formulas= formula_translation(_rules)
		#print("_Formulas___________________________________________________________")
		#for f in _formulas:
		#	print(f)
		comIorg = get_com_org_imp(propositions)
		condition = create_condition(formulas, _formulas, comIorg)
		#print("condition______________________________________________________________")
		#print(condition)
		YY = satisfiable(condition, all_models = True)
		listYY = list(YY)
		print("\n")
		model = get_Models(listYY)
		return model


def get_file():				
	while True:
		file_name = input("Please input the name of a text-file containing a set of rules \n")
		if file_name.endswith(".txt") == False:
			file_name = file_name + ".txt"
		if(os.path.exists(file_name)):
			_file = open(file_name, "r+")
			print("Name of file: %s \n" % (file_name))
			res = [_file, file_name]
			return res
		else:
			print("The file you selected does not exist, please try again\n")
			print("(Or press 'r' to return) \n ")
			name = input()
			if name == 'r':
				res = []
				return res

def obtain_atomic_formulas(file):				#Scans through the input file collecting distinct atomic formulas 
	propositions = set()
	lines = (line.rstrip() for line in file)
	lines = (line for line in lines if line)
	flag = False
	for line in lines:
		if line.startswith("#") or second in line:
			continue
		add_proposition(line, propositions)
	return propositions

def add_proposition(line, propositions): 				#Add atomic formulas when new rule is added
	_line = re.sub(r'\s+', '', line)
	_line = _line.replace(".", ",")
	_line = _line.replace("&", ",")
	_line = _line.replace(";", ",")
	_line = _line.replace("|", ",")
	_line = _line.replace("->", ",")
	_line = _line.replace("=>", ",")
	_line = _line.replace("~", "")
	_line = _line.replace("!", "")
	_line = _line.replace(":-", ",")
	_line = _line.replace("::=", ",")
	_line = _line.replace("(", "")
	_line = _line.replace(")", "")
	_line = _line.replace("not", "")
	_line = _line.replace("TRUE", "")
	_line = _line.replace("FALSE", "")
	_line = _line.replace("1", "")
	_line = _line.replace("0", "")
	_line = _line.replace("+", ",")
	_line = _line.replace("*", ",")
	new_props = _line.split(",")
	new_props = list(filter(None, new_props))
	for prop in new_props: 
		new = Symbol(prop)
			#_new = Symbol("_" + prop)
		propositions.add(new)

def _mapping(propositions):
	mapping = {}
	for p in propositions:
		if "_" in str(p):
			continue
		else:
			corra = Symbol("_" + p)
			mapping[p] = corra
	return mapping

def construct_program(file, pro):					# Scans through the input file parsing out individual rules and their \
														#components 
	flag = False
	rules = {}
	count = 0
	lines = (line.rstrip() for line in file) # All lines including the blank ones
	lines = (line for line in lines if line)
	#print("Lines")
	for line in lines:
		if pro == "A":
			if second in line:
				return rules
		if pro == "B":
			if second in line:
				flag = True
				continue
			if flag == False:
				continue
		if line.startswith("#"):
			continue
		add_rule(line, rules)
	return rules


def add_rule(rule, rules):					# Adds a rule to an existing program or one that is under construction 
		count = len(rules.keys())
		head = ""
		pos_body = []
		neg_body = []
		name = "r" + str(count)
		_line = re.sub(r'\s+', '', rule)	
		_line = _line.strip()
		_line = _line.replace(".", "")
		
		if ":-" not in _line and "::=" not in _line:
			_line = _line.replace(".", "")
			head = _line
		elif _line.startswith(":-") or _line.startswith("FALSE") or _line.startswith("0") or _line.startswith("::="):
			if _line.startswith("FALSE"):
				head = "FALSE"
			if _line.startswith("0"):
				head = "0"
			body = _line.replace(":-", "")
			body = body.replace("::=", "")
			body = body.replace("FALSE", "")
			body = body.replace("0", "")
			#print("Line: %s" % (body))
			if "." not in body:
				if body.startswith("not"):
					neg_body.append(body)
				else:
					pos_body.append(body)
			else:
				body = div[1].split(".")
				for b in body:
					if b.startswith("not"):
						neg_body.append(b)
					else:
						pos_body.append(b)
		elif _line.endswith(":-") or _line.endswith("TRUE") or _line.endswith("1") or _line.endswith("::="):
			head = _line.replace(":-", "")
			head = head.replace("::=", "")
			head = head.replace("TRUE", "")
			head = head.replace("1", "")
			if head.endswith("TRUE"):
				pos_body = "TRUE"
			if head.endswith("1"):
				pos_body = "1"
		else:
			if ":-" in _line:
				div = _line.split(":-")
			if "::=" in _line:
				div = _line.split("::=")
			head = div[0]
			#print("head: %s" % (head))
			if "." not in div[1]:
				#print("No . in body")
				if div[1].startswith("not"):
				#	print("starts with not")
					neg_body.append(div[1])
				else:
					pos_body.append(div[1])
			else:
				#print("Has . in body")
				body = div[1].split(".")
				for b in body:
					if b.startswith("not"):
						neg_body.append(b)
					else:
						pos_body.append(b)
		name = "r" + str(count)
		new = Rule(name, rule, head, pos_body, neg_body)
		rules.update({name: new})

def formula_translation(rules):				#Translates rules into propositional logic formulas using "&" for AND,
	formulas = []							# "|" for OR and "~" for NOT
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
			if "->" in pante:
				imp = pante.split("->")
				pante = "~" + imp[0] + "|" + imp[1]
			if "=>" in pante:
				imp = pante.split("=>")
				pante = "~" + imp[0] + "|" + imp[1]
			for char in pante:
				char = Symbol(char)
			#print("3: %s" % (pante))
			pante = simplify(pante)
			if len(rule.pos_body) > 1:
				count = 1
				while count < len(rule.pos_body):
					#print(count)
					add = str(rule.pos_body[count]).replace("not", "~")
					add = add.replace("!", "~")
					add = add.replace(";", "|")
					#print("2: %s" % (add) )
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
					if "=>" in add:
						imp = add.split("=>")
						add = "~" + imp[0] + "|" + imp[1]
					for char in add:
						char = Symbol(char)
					add = simplify(add)
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
			ant = Not(ante)
			#print(ante)
			formulas.append(ant)
	return formulas

def rule_compliment(rules, propositions):	#Each rule is given a "compliment" with propositions that correspond
	crules = []								# to those given in the original program. For each p the correspondent
	for r, rule in rules.items():			# is _p. The resulting compliment formulas are needed to calculate
		new = ""							# the SE models
		_temp = str(rule.item)
		temp = re.sub(r'\s+', '', _temp)
		temp = temp.strip('')
		for p in propositions:
			if str(p).startswith("_"):
				continue
			elif str(p) in temp:
				ex = "_" + str(p)
				#print(ex)
				temp = temp.replace(str(p), ex)
				temp = temp.replace("~" + ex, "~" + str(p))
				temp = temp.replace("not" + ex, "not" + str(p))
				temp = temp.replace("!" + ex, "!" + str(p))
		crules.append(temp)
	return crules



def get_com_org_imp(propositions):		#For each proposition p we introduce _p -> p 
	comIorg = []
	for p in propositions:
		if "_" not in str(p):
			temp = "~_"+ str(p) + "|" + str(p)
			for char in temp:
				char = Symbol(temp)
			temp = simplify(temp)
			comIorg.append(temp)
	return comIorg

def create_condition(formulas, _formulas, comIorg): #The condition is comprised of (1) each formula derived from the 
	conditions = comIorg[0]							# program, (2) the "compliments" of those rules, and (3) each 
	for f in formulas:								# _p -> p formula. Every interpretation that satisfies this 
		conditions = And(f, conditions)				# condition will be a model.
	for _f in _formulas:
		conditions = And(_f, conditions)
	for cio in comIorg:
		conditions = And(cio, conditions)
	return conditions

def get_Models(listYY):							# The (X, Y) models are derived from the output of the previous function.
	models = set()								# Y values are directly from those values. The X values are obtained
	count = 0									# as follows: when _p is true in an Y model, p is also true. Since  
	if len(listYY) == 1 and listYY[0] == False:	# _p -> p, we know that X will be a subset of Y.
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
			models.add(new)
			count += 1
		return models

def get_se_model(model):					#Gathers up the se_models as a set of sets 
			se_model = set()
			for m in model:
				item = frozenset(m.XY)
				se_model.add(item)
			return se_model 


def create_txt_single(model):			 #	Creates text file of SE models of a single program		
	print("Please provide a name for the new file\n")
	text_name = input()
	text_name = text_name + ".txt"
	save = open(text_name, 'a+')
	save.write("\n")
	save.write("__________________________________________________\n ")
	save.write("SE Models \n")
	save.write("__________________________________________________ \n \n")
	for m in model:
		save.write("< %s, %s > \n" % (m.X, m.Y))
	save.write("\n")
	save.write("__________________________________________________ \n \n")
	print("\n")
	print("%s has been written to disk\n" % (text_name))
	save.close()
	return save 

def create_txt_double(modelA, modelB):  # Creates text file of SE models from two program files
	print("Please provide a name for the new file\n")
	text_name = input()
	text_name = text_name + ".txt"
	save = open(text_name, 'a+')
	save.write("\n")
	save.write("__________________________________________________ \n")
	save.write("SE Models \n")
	save.write("__________________________________________________ \n \n")
	save.write("Program A:")
	save.write("\n")
	for m in modelA:
		save.write("< %s, %s > \n" % (m.X, m.Y))
	save.write("\n")
	save.write("Program B:")
	save.write("__________________________________________________ \n \n")
	save.write("\n")
	for m in modelB:
		save.write("< %s, %s > \n" % (m.X, m.Y))
	save.write("\n")
	print("\n")
	save.write("__________________________________________________ \n \n")
	print("%s has been written to disk\n" % (text_name))
	save.close()
	return save

#def print_models(data):
	#print("Which printer would you like to use?")
	#printers = win32print.EnumPrinters(5)
	#for p in printers:
	#	print(p)
	#printer_name = input()

#	data = open("temp-file1324.txt", "rb").read () + b"\x0c"
	
#	printer_name = win32print.GetDefaultPrinter()
#	printer = win32print.OpenPrinter (printer_name)
#	try:
#		job = win32print.StartDocPrinter(printer, 1, ("test of raw data", None, "RAW"))
#		try:
#			win32print.StartPagePrinter (printer)
#			win32print.WritePrinter (printer, data)
#			win32print.EndPagePrinter (printer)
#		finally:
#			win32print.EndDocPrinter (printer)
#	finally:
#		win32print.ClosePrinter (printer)


def results(modelA, modelB):		# Prints results to user on the command line

	print("\n")
	print("----------------------------------------------------------------------------------")
	print(" A Models:")
	print("----------------------------------------------------------------------------------")
	rep = "{"+"}"
	for m in modelA:
		if str(m.X) == "set()":
			m.X = rep
		if str(m.Y) == "set()":
			m.Y = rep
		print("< %s, %s >" % (m.X, m.Y))
	print("\n")
	print("----------------------------------------------------------------------------------")
	print(" B Models:")
	print("----------------------------------------------------------------------------------")
	for m in modelB:
		if str(m.X) == "set()":
			m.X = rep
		if str(m.Y) == "set()":
			m.Y = rep
		print("< %s, %s >" % (m.X, m.Y))
	print("\n")

	se_modelA = get_se_model(modelA)
	se_modelB = get_se_model(modelB)


	if se_modelA == se_modelB:
		print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
		print("The the programs are strongly equivalent")
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
		print("The programs are not strongly equivalent and it is not the case that one entails the other")
		print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
	print("\n")



def augment_programA(augment, file):		#Add rule to the first (or only) program
	with open(file, "r+") as f:
		f.seek(0, 0)
		f.write(augment)
		f.close

def augment_programB(augment, file):		#Add a rule to the second program
	file = open(file, "a+")
	file.write(augment)
	file.close()

def get_rule_name_from_item(item, rules):		# Auxiliary function
	name = ""
	for k, v in rules.items():
		temp = re.sub(r'\s+', '', v.item)
		temp = temp.strip
		if item == temp:
			name = k
	return k


		
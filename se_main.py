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
	for line in file:
		if line.startswith("#"):
			continue
		print("Line: %s" % (line))
		_line = re.sub(r'\s+', '', line)	
		_line = _line.strip()
		print("_Line: %s" % (_line))
		div1 = _line.split(":-")
		head = div1[0]
		print("div1[0]: %s" % (div1[0]))
		print("div1[1]: %s" % (div1[1]))
	
		body = div1[1].split(".")
		pos_body = []
		neg_body = []
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
		if len(rule.pos_body) > 0:
			pante = str(rule.pos_body[0]).replace("not", "~")
			pante = symbols(pante)
			if "->" in str(rule.pos_body[0]):
				imp = str(rule.pos_body[0]).split("->")
				pante = "~" + imp[0] + "|" + imp[1]
			if len(rule.pos_body) > 1:
				count = 1
				while count <= len(rule.pos_body):
					add = str(rule.pos_body[count]).replace("not", "~")
					if "->" in str(rule.pos_body[count]):
						imp = str(rule.pos_body[count]).split("->")
						imp[0] =  "~" + imp[0]
						add = imp[0] + "|" + imp[1]
					add = symbols(add)
					pante = And(pante, add)
					count += 1
		if len(rule.neg_body) > 0:
			nante = str(rule.neg_body[0]).replace("not", "~")
			nante = symbols(nante)
			if "->" in str(rule.neg_body[0]):
				imp = str(rule.neg_body[0]).split("->")
				pante = "~" + imp[0] + "|" + imp[1]
			if len(rule.neg_body) > 1:
				count = 1
				while count <= len(rule.neg_body):
					add = rule.neg_body[count].replace("not", "~")
					if "->" in str(rule.neg_body[count]):
						imp = str(rule.neg_body[count]).split("->")
						add = "~" + imp[0] + "|" + imp[1]
					add = symbols(add)
					nante = And(nante, add)
					count += 1
		if pante:
			pante = to_cnf(pante)
		if nante: 
			nante = to_cnf(nante)
		if pante and nante:		
			ante = And(pante, nante)
		else:
			if pante:
				ante = pante
			else:
				ante = nante
		ante = Not(ante)
		con = ""
		if rule.head:
			con = to_cnf(rule.head)
		print("Con: %s " %(con))
		print("ante: %s "% (ante))

		f = Or(ante, con)
		formulas.append(f)
	return formulas

def rule_compliment(rules, propositions):
	_rules = {}
	for r, rule in rules.items():
		new = ""
		for p in propositions:
			temp = str(rule.item)
			if str(p) in temp:
				print("In temp %s " % (str(p)))
				ex = "_" + str(p)
				print(ex)
				temp1 = temp.replace(str(p), ex)
				print("temp1: %s" % (temp1))
				temp2 = temp1.replace("~" + ex, "~" + str(p))
				new = Symbol(temp2)
		_rules[r] = new
	return _rules



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
	_rules = rule_compliment(rules, propositions)

	_formulas = formula_compliment(formulas, propositions)

	print("Lets see what just happened_________________________________________________________________________")

	print("formulas:")
	for f in formulas:
		print(f)
	print("_________ _rules:")
	for rule in _rules.values():
		print(rule)

#Now that we have the rules of the program P stored, we need to construct gamma(P).



	
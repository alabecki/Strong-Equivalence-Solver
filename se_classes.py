#Classes

class Rule(object):
	def __init__(self, _name, _item, _head, _pos_body, _neg_body):
		self.name = _name							
		self.item = _item							
		self.pos_body = _pos_body
		self.neg_body = _neg_body							
		self.head = _head						
		self.bodyExtension = []					
		self.headExtension = []						
									

class Model(object):
	def __init__ (self, name, Y, X, XY):
		self.name = name
		self.Y = Y
		self.X = X
		self.XY = XY
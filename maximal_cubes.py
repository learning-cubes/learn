import z3
from z3 import *
import time
import sys
'''
Class cube saves minimal corner and maximal corner.
There are a few ways to save this:
1. Quick and dirty: Just save the corner as a z3 formula.
   Problem: How do I extract this corner again and how do I add +1 on 
   coordinates?
2. Trust in no errors and save the coordinates for each point in a list 
for each corner.
   Advantage: Easy handling for each coordinate.
              You do not need to save = or <= and just use whatever you 
              need when constructing the cube.
   Problem: Can easily add to errors if length of lists are not the same. 
   
Useful class methods: 
build_cube_formula(), where you return a formula representing the cube,
 alternatively just create it once and save as a class variable
 
__str__ where you return the endpoints

get and set possibly for each corner
'''
class Cube:
	def __init__(self, min_corner, max_corner,variables):
		self.min_corner = min_corner
		self.max_corner = max_corner
		self.variables = variables
		self.cube_formula = True
	
	def get_min_corner(self):
		return self.min_corner
		
	def get_max_corner(self):
		return self.max_corner		

	def get_cube_formula(self):
		# For now assume corners are given as list and build z3 formula out of it
		if self.cube_formula == True:
			for i in range(0,len(self.min_corner)):
				self.cube_formula = And(self.cube_formula, self.min_corner[i] <= self.variables[i])
			for i in range(0,len(self.max_corner)):
				self.cube_formula = And(self.cube_formula, self.variables[i] <= self.max_corner[i])
		return self.cube_formula
		
'''
Class teacher resolves query and requests from the learner.
All queries to z3 are handled in this class.

Methods:

equivalence query(hyp, target), returns a counterexample if hyp != target

subset query(cube, target), returns yes if the cube is a subset of the target


'''

class Teacher:
	def __init__(self, variables,target, smt = False):
		# maybe create a z3 solver?
		self.solver = Solver()
		self.variables = variables
		self.target = target
		
	def equivalence_query(self,hyp):
		#print("Equivalence query on ", hyp, " \n with target: \n ", self.target)
		self.solver.add(Xor(hyp, self.target))
		if self.solver.check() == z3.sat:
			m = self.solver.model()
			#print("Model, i.e. counterexample" , m )
			counterexample = []
			for v in self.variables:
				#print(v, "= ", m.eval(v, model_completion=True))
				# todo cast to python int
				#print(m[x])
				counterexample.append( int((m.eval(v, model_completion=True)).as_string()))
				#counterexample.append((m.eval(v, model_completion=True)))
			self.solver.reset()
			return (False, counterexample)
		self.solver.reset()
		return (True, False)
	
	''' Method subset_query takes hyp_cube as an input which is a z3
	    formula representing the hypothesis cube and the target set also
	    represented by a z3 formula. It computes whether hyp_cube ⊆ target.
	    It returns True if this is the case, and False if this is not the case.'''
	def subset_query(self,hyp_cube):
		#print("Subset query on ", hyp_cube, " ", self.target)
		query = Implies(hyp_cube, self.target)
		query = Not(query)
		self.solver.add(query)
		#print(self.solver.check())
		if self.solver.check() == z3.unsat:
			self.solver.reset()
			#print("Subset query success!")
			return True
		else:
			self.solver.reset()
			#print("Subset query fail!")
			return False
		
		
	''' DEPRECATED: analogous to subset_query but hyp_point is just one point instead of a cube'''
	def membership_query(self,hyp_point):
		#print("Membership query on ", hyp_point, " ", self.target)
		query = Implies(hyp_point, self.target)
		query = Not(query)
		self.solver.add(query)
		if self.solver.check() == z3.unsat:
			self.solver.reset()
			return True
		else:
			self.solver.reset()
			return False
		

'''
Class learner learns the target set by representing it with cubes.

Question: Do we need to state the dimension of what we learn somewhere?
          You could get it indirectly from the counterexamples possibly.
 
Methods:
learn() this is the main method which will make use of other methods to
        construct an hypothesis and query the teacher.
        
Initialize with hyp = false and equivalence query to obtain the first
counterexample. From this point we need to learn the maximal cube.
We will refer to this step to a method called learn_maximal_cube(v)
where v is a point.
Once the maximal cube is learnt the learner can ask an equivalence query
to the teacher. Over many iterations the learner will store the learnt 
cubes in the hypothesis and not change them again, only add more cubes.

learn_maximal_cube(v): given a point, we need to determine the maximal
and the minimal corner. We could try to do this with standard binary
search or try to come up with an z3 formula.

'''

class Learner_max_cubes:
	def __init__(self, variables, unary = True, binary = False, optimized = False):
		self.max_cubes = []
		self.variables = variables
		self.counterexamples = []
		self.hypothesis = False
		self.unary = unary
		self.binary = binary
		self.optimized = optimized
		self.var_bar = []
		for i in range (0,len(self.variables)):
			placeholder = Int(i)
			self.var_bar.append(placeholder)
		self.no_upper_bound = []
		for i in range (0,len(self.variables)):
			self.no_upper_bound.append(False)
		self.no_lower_bound = []
		for i in range (0,len(self.variables)):
			self.no_lower_bound.append(False)

		
		
	def build_point_formula(self, point):
		formula = True
		for coordinate in range(0,len(point)):
			formula = And(formula, point[coordinate] == self.variables[coordinate])
		return formula	
		
		
	def learn(self, teacher):
		# query teacher for a counterexample
		# extend counterexample to max cube
		# get new counterexample until done
		is_hypothesis_correct = False
		while (not is_hypothesis_correct):			
			teacher_reply = teacher.equivalence_query(self.build_hypothesis())
			is_hypothesis_correct = teacher_reply[0]
			self.counterexamples.append(teacher_reply[1])
			if (teacher_reply[1] == False):
				pass
			else: 
				if self.unary:
					max_cube_formula = self.learn_maximal_cube_unary2(teacher_reply[1], teacher)
				elif self.binary:
					max_cube_formula = self.learn_maximal_cube_binary2(teacher_reply[1], teacher)
				elif self.optimized:
					max_cube_formula = self.learn_maximal_cube_optimized_unbounded(teacher_reply[1], teacher, 5)
				else:
					print(self.optimized)
					print ("ERROR")
				self.max_cubes.append(max_cube_formula)
		return self.max_cubes
			
		
		
		
	def learn_maximal_cube_unary(self,counterexample, teacher):
		''' 1. do unary search over all points to check if cube can be made bigger
		 2. do binary search over all points to check if cube can be made bigger
		 do unary search method first, as long as all variables give a true
		 subset query we can increase the unary jump by one
		'''
		max_corner = counterexample.copy()
		start_point = self.build_lower_corner(counterexample)
		
		for i in range(0,len(self.variables)):
			is_corner_found = False
			while is_corner_found == False:
				# do subset query with modified corner, if subset is false then we already had corner
				max_corner[i] = max_corner[i] + 1
				if i == 0:
					is_corner_found = not teacher.membership_query(self.build_point_formula(max_corner))
				else:
					cube_formula = And(start_point, self.build_upper_corner(max_corner))	
					is_corner_found = not teacher.subset_query(cube_formula)
			max_corner[i] = max_corner[i] -1
		min_corner = counterexample.copy()
		start_point = self.build_upper_corner(max_corner)
		for i in range(0,len(self.variables)):
			is_corner_found = False
			while is_corner_found == False:
				# do subset query with modified corner, if subset is false then we already had corner
				min_corner[i] = min_corner[i] - 1
				cube_formula = And(start_point, self.build_lower_corner(min_corner))
				is_corner_found = not teacher.subset_query(cube_formula)
			min_corner[i] = min_corner[i] +1	
		return And(self.build_lower_corner(min_corner),self.build_upper_corner(max_corner))

	def learn_maximal_cube_unary2(self,counterexample, teacher):
		''' 1. do unary search over all points to check if cube can be made bigger
		 2. do binary search over all points to check if cube can be made bigger
		 do unary search method first, as long as all variables give a true
		 subset query we can increase the unary jump by one
		'''
		#print("\n\n COUNTEREXAMPLE: \n ", counterexample, "\n\n")
		max_corner = counterexample.copy()
		min_corner = counterexample.copy()
		
		for i in range(0,len(self.variables)):
			is_max_corner_found = False
			is_min_corner_found = False
			while not(is_max_corner_found and is_min_corner_found):
				# do subset query with modified corner, if subset is false then we already had corner
				#print(max_corner, min_corner)
				if is_max_corner_found:
					pass
				else:
					start_point = self.build_lower_corner(min_corner)
					max_corner[i] = max_corner[i] + 1
					if i == 0:
						is_max_corner_found = not teacher.membership_query(self.build_point_formula(max_corner))
						if is_max_corner_found:
							max_corner[i] = max_corner[i] -1
					else:
						
						cube_formula = And(start_point, self.build_upper_corner(max_corner))	
						is_max_corner_found = not teacher.subset_query(cube_formula)
						if is_max_corner_found:
							max_corner[i] = max_corner[i] -1
				if is_min_corner_found:
					pass
				else:
					start_point_1 = self.build_upper_corner(max_corner)
					min_corner[i] = min_corner[i] - 1
					if i == 0:
						
						is_min_corner_found = not teacher.membership_query(self.build_point_formula(min_corner))
						if is_min_corner_found:
							min_corner[i] = min_corner[i] +1
					else:
						cube_formula = And(start_point_1, self.build_lower_corner(min_corner))	
						is_min_corner_found = not teacher.subset_query(cube_formula)
						if is_min_corner_found:
							min_corner[i] = min_corner[i] +1	
		return And(self.build_lower_corner(min_corner),self.build_upper_corner(max_corner))
	
	def z3_abs(self,x):
		return If(x >=0, x, -x)
		
	def learn_maximal_cube_unary_deprecated(self,counterexample, teacher):
		''' 1. Instead of doing subset queries, we will do membership queries
		to extend the point to a cube. To do this we start off initially with 
		one point, the counterexample (e.g. [0,0]). Then we for each var (x,y)
		we extend the point in direction [1, -1]. As long as the mem query is 
		positive we keep going and add it to the set of expandable points.
		Lets say we end up with [[1,0][-1,0]], the points [2,0] and [-2,0]
		were negative.
		We add all positive positive points to the total set of expandable 
		points, we get [[0,0],[1,0],[-1,0]].
		This is the start set for our next variable, y.
		In on step we increase y by 1 for all points and check mem, i.e., 
		check [0,1],[1,1] and [-1,1]. Only if all mem are positive we keep 
		going and add those points to all expandable points.
		This is again done for +1 and -1 for y and in the end all expandable
		points are combined to one set for the next set. 
		2. There are two ways to get the max cube from this.
			2.1 Combine all points from expandable points to a cube.
			2.2 Save the max x,y and min x,y when doing the algo and in the
				end build the cube from those coordinates.
		'''
		expandable_points = []
		expandable_points.append(counterexample)
		max_point = []
		min_point = []
		for var in range(0, len(self.variables)):
			temp_expand = []
			for i in [1,-1]:
				all_are_members = True		
				temp_temp_expand = []
				distance = 0
				while all_are_members:
					if not temp_temp_expand == []:
						#print("Add temp_temp_expand to temp_expand: ", temp_temp_expand)
						temp_expand = temp_expand + temp_temp_expand
					distance += 1
					temp_temp_expand = []
					for point in expandable_points:
						temp_point = point.copy()
						temp_point[var] = point[var] + i * distance
						#print("Testing point: ", temp_point)
						if teacher.membership_query(self.build_point_formula(temp_point)):
							#print("True")
							temp_temp_expand.append(temp_point)
						else:
							#print("False")
							if i == 1:
								max_point.append(temp_point[var] -1)
							else:
								min_point.append(temp_point[var] +1)
							all_are_members = False
							break
			expandable_points = expandable_points + temp_expand
			#print("exp points update: ", expandable_points)
			#print(max_point, " ", min_point)
			
		return And(self.build_upper_corner(max_point), self.build_lower_corner(min_point))
		
		
	def find_corner_unary(self, counterexample, teacher, max = True):
		max_corner = counterexample.copy()
		if max == True:
			for i in range (0,len(self.variables)):
				is_corner_found = False
				while is_corner_found == False:
					max_corner[i] = max_corner[i] +1
					is_corner_found = not teacher.membership_query(self.build_point_formula(max_corner))
				max_corner[i] = max_corner[i] -1
			return max_corner
		else: 
			for i in range (0,len(self.variables)):
				is_corner_found = False
				while is_corner_found == False:
					max_corner[i] = max_corner[i] -1
					is_corner_found = not teacher.membership_query(self.build_point_formula(max_corner))
				max_corner[i] = max_corner[i] +1
			return max_corner
			
		
	def binary_search(self,low_point, high_point, i, teacher, corner_formula, max = True):
		mid_point = low_point.copy()
		while low_point[i] != high_point[i]:
			if max:
				mid_point[i] = math.ceil((low_point[i] + high_point[i]) /2)
			else:
				mid_point[i] = math.floor((low_point[i] + high_point[i]) /2)
			if max:
				is_sub_set = teacher.subset_query(And(corner_formula, self.build_upper_corner(mid_point)))
			else:
				is_sub_set = teacher.subset_query(And(corner_formula, self.build_lower_corner(mid_point)))
			mid_point[i] = ((low_point[i] + high_point[i]) /2)
			if max:
				if is_sub_set:
					low_point[i] = math.ceil(mid_point[i])
					mid_point[i] = math.ceil(mid_point[i])
				else:
					high_point[i] = math.floor(mid_point[i])
					mid_point[i] = math.floor(mid_point[i])
			else:
				if not is_sub_set:
					low_point[i] = math.ceil(mid_point[i])
					mid_point[i] = math.ceil(mid_point[i])
				else:
					high_point[i] = math.floor(mid_point[i])
					mid_point[i] = math.floor(mid_point[i])
		return mid_point
			
	def learn_maximal_cube_binary(self,counterexample, teacher):
		''' 1. do unary search over all points to check if cube can be made bigger
		 2. do binary search over all points to check if cube can be made bigger
		 do unary search method first, as long as all variables give a true
		 subset query we can increase the unary jump by one
		'''
		#print("\n\n\n Counterexample: " , counterexample, "\n\n\n", self.max_cubes)
		max_corner = counterexample.copy()
		lower_bound = counterexample.copy()
		start_point = self.build_lower_corner(counterexample)
		
		for i in range(0,len(self.variables)):
			is_corner_found = False
			is_upper_bound = False
			# find a max for binary search
			stepsize = 1
			while not is_upper_bound:
				'''
				have stepsize defined before, stepsize = 1, then add stepsize
				then do subset query and multiply stepsize by 2
				keep doing it as long as the subset query is positive
				the last positive one is the lower bound and the latest negative
				is the upper bound
				goal is to determine something in between which is positive
				'''
				max_corner[i] = max_corner[i] + stepsize
				cube_formula = And(start_point, self.build_upper_corner(max_corner))
				is_upper_bound = not teacher.subset_query(cube_formula)
				stepsize = stepsize * 2
			stepsize = int(stepsize / 2)
			lower_bound[i] = max_corner[i] - stepsize
			max_corner = self.binary_search(lower_bound, max_corner, i, teacher, start_point)
			
		min_corner = counterexample.copy()
		upper_bound = counterexample.copy()
		start_point = self.build_upper_corner(max_corner)
				
		for i in range(0,len(self.variables)):
			is_corner_found = False
			is_lower_bound = False
			while not is_lower_bound:
				'''
				have stepsize defined before, stepsize = 1, then add stepsize
				then do subset query and multiply stepsize by 2
				keep doing it as long as the subset query is positive
				the last positive one is the lower bound and the latest negative
				is the upper bound
				goal is to determine something in between which is positive
				'''
				min_corner[i] = min_corner[i] - stepsize
				cube_formula = And(start_point, self.build_lower_corner(min_corner))
				is_lower_bound = not teacher.subset_query(cube_formula)
				stepsize = stepsize * 2
			stepsize = stepsize / 2
			upper_bound[i] = min_corner[i] + stepsize
			#print("\n LOWER BOUND \nlower bound var: ", min_corner[i], " upper bound var: ", upper_bound[i])
			min_corner = self.binary_search(min_corner, upper_bound, i, teacher, start_point, max = False)
			
		return And(self.build_lower_corner(min_corner),self.build_upper_corner(max_corner))
	
	def learn_maximal_cube_binary2(self,counterexample, teacher):
		''' 1. do unary search over all points to check if cube can be made bigger
		 2. do binary search over all points to check if cube can be made bigger
		 do unary search method first, as long as all variables give a true
		 subset query we can increase the unary jump by one
		'''
		#print("\n\n\n Counterexample: " , counterexample, "\n\n\n", self.max_cubes)
		max_corner = counterexample.copy()
		lower_bound = counterexample.copy()
		start_point = self.build_lower_corner(counterexample)
		min_corner = counterexample.copy()
		upper_bound = counterexample.copy()
		
		for i in range(0,len(self.variables)):
			#print(max_corner, min_corner)
			is_corner_found = False
			is_upper_bound = False
			is_lower_bound = False
			# find a max for binary search
			stepsize = 1
			while not (is_upper_bound):
				'''
				have stepsize defined before, stepsize = 1, then add stepsize
				then do subset query and multiply stepsize by 2
				keep doing it as long as the subset query is positive
				the last positive one is the lower bound and the latest negative
				is the upper bound
				goal is to determine something in between which is positive
				'''
				max_corner[i] = max_corner[i] + stepsize
				cube_formula = And(self.build_lower_corner(min_corner), self.build_upper_corner(max_corner))
				is_upper_bound = not teacher.subset_query(cube_formula)
				stepsize = stepsize * 2
			stepsize = int(stepsize / 2)
			lower_bound[i] = max_corner[i] - stepsize
			max_corner = self.binary_search(lower_bound, max_corner, i, teacher, self.build_lower_corner(min_corner))
			
			stepsize = 1
			while not (is_lower_bound):
				'''
				have stepsize defined before, stepsize = 1, then add stepsize
				then do subset query and multiply stepsize by 2
				keep doing it as long as the subset query is positive
				the last positive one is the lower bound and the latest negative
				is the upper bound
				goal is to determine something in between which is positive
				'''
				min_corner[i] = min_corner[i] - stepsize
				cube_formula = And(self.build_upper_corner(max_corner), self.build_lower_corner(min_corner))
				is_lower_bound = not teacher.subset_query(cube_formula)
				stepsize = stepsize * 2
			stepsize = stepsize / 2
			upper_bound[i] = min_corner[i] + stepsize
			#print("\n LOWER BOUND \nlower bound var: ", min_corner[i], " upper bound var: ", upper_bound[i])
			min_corner = self.binary_search(min_corner, upper_bound, i, teacher, self.build_upper_corner(max_corner), max = False)
			#print(max_corner, min_corner)
		return And(self.build_lower_corner(min_corner),self.build_upper_corner(max_corner))				
			
			
		min_corner = counterexample.copy()
		upper_bound = counterexample.copy()
		start_point = self.build_upper_corner(max_corner)
				
		for i in range(0,len(self.variables)):
			is_corner_found = False
			is_lower_bound = False
			while not is_lower_bound:
				'''
				have stepsize defined before, stepsize = 1, then add stepsize
				then do subset query and multiply stepsize by 2
				keep doing it as long as the subset query is positive
				the last positive one is the lower bound and the latest negative
				is the upper bound
				goal is to determine something in between which is positive
				'''
				min_corner[i] = min_corner[i] - stepsize
				cube_formula = And(start_point, self.build_lower_corner(min_corner))
				is_lower_bound = not teacher.subset_query(cube_formula)
				stepsize = stepsize * 2
			stepsize = stepsize / 2
			upper_bound[i] = min_corner[i] + stepsize
			#print("\n LOWER BOUND \nlower bound var: ", min_corner[i], " upper bound var: ", upper_bound[i])
			min_corner = self.binary_search(min_corner, upper_bound, i, teacher, start_point, max = False)
			
		return And(self.build_lower_corner(min_corner),self.build_upper_corner(max_corner))	
	
		
	def learn_maximal_cube_optimized(self, counterexample, teacher, cutoff_value):
		'''
		Mix the unary and binary approach and also check for unboundedness
		in between
		
		1.  start off like the unary approach, increase the value cutoff_value
			times. If we terminate early or on time we set a flag that this variable
			is done. Otherwise we continue with the other approaches on the same variable
		2.  Next, check if the variable is unbounded, this is one check were we either
			have no upper or lower bound of the variable depending on whether we compute
			the min or max corner. Set a flag if the variable is indeed unbounded.
		3.  Finally, accelerate to binary search to find the corner.
		'''
		
		max_corner = counterexample.copy()
		min_corner = counterexample.copy()
		
		for i in range(0,len(self.variables)):
			is_max_corner_found = False
			is_min_corner_found = False
			counter = 0
			while (not(is_max_corner_found and is_min_corner_found))  and counter < cutoff_value:
				counter += 1
				# do subset query with modified corner, if subset is false then we already had corner
				#print(max_corner, min_corner)
				if is_max_corner_found:
					pass
				else:
					start_point = self.build_lower_corner(min_corner)
					max_corner[i] = max_corner[i] + 1
					if i == 0:
						is_max_corner_found = not teacher.membership_query(self.build_point_formula(max_corner))
						if is_max_corner_found:
							max_corner[i] = max_corner[i] -1
					else:
						
						cube_formula = And(start_point, self.build_upper_corner(max_corner))	
						is_max_corner_found = not teacher.subset_query(cube_formula)
						#print("is max_corner found?: ",  is_max_corner_found, max_corner)
						if is_max_corner_found:
							max_corner[i] = max_corner[i] -1
				if is_min_corner_found:
					pass
				else:
					start_point_1 = self.build_upper_corner(max_corner)
					min_corner[i] = min_corner[i] - 1
					if i == 0:
						
						is_min_corner_found = not teacher.membership_query(self.build_point_formula(min_corner))
						#print(is_min_corner_found)
						if is_min_corner_found:
							min_corner[i] = min_corner[i] +1
					else:
						cube_formula = And(start_point_1, self.build_lower_corner(min_corner))	
						is_min_corner_found = not teacher.subset_query(cube_formula)
						#print("is min_corner found?: ",  is_min_corner_found, min_corner)
						if is_min_corner_found:
							min_corner[i] = min_corner[i] +1	
			# leaving while loop
			lower_bound = max_corner.copy()
			upper_bound = min_corner.copy()
			if not(is_max_corner_found):
				# check unbounded first? no, write new method for unbounded checks only
				stepsize = 1
				is_upper_bound = False
				
				while not (is_upper_bound):
					max_corner[i] = max_corner[i] + stepsize
					cube_formula = And(self.build_lower_corner(min_corner), self.build_upper_corner(max_corner))
					is_upper_bound = not teacher.subset_query(cube_formula)
					stepsize = stepsize * 2
				stepsize = int(stepsize / 2)
				lower_bound[i] = max_corner[i] - stepsize
				max_corner = self.binary_search(lower_bound, max_corner, i, teacher, self.build_lower_corner(min_corner))
			if not(is_min_corner_found):
				stepsize = 1
				is_lower_bound = False
				while not (is_lower_bound):
					min_corner[i] = min_corner[i] - stepsize
					cube_formula = And(self.build_upper_corner(max_corner), self.build_lower_corner(min_corner))
					is_lower_bound = not teacher.subset_query(cube_formula)
					stepsize = stepsize * 2
				stepsize = stepsize / 2
				upper_bound[i] = min_corner[i] + stepsize
				min_corner = self.binary_search(min_corner, upper_bound, i, teacher, self.build_upper_corner(max_corner), max = False)
				
		return And(self.build_lower_corner(min_corner),self.build_upper_corner(max_corner))
		
	def learn_maximal_cube_optimized_unbounded(self, counterexample, teacher, cutoff_value):
		'''
		Mix the unary and binary approach and also check for unboundedness
		in between
		
		1.  start off like the unary approach, increase the value cutoff_value
			times. If we terminate early or on time we set a flag that this variable
			is done. Otherwise we continue with the other approaches on the same variable
		2.  Next, check if the variable is unbounded, this is one check were we either
			have no upper or lower bound of the variable depending on whether we compute
			the min or max corner. Set a flag if the variable is indeed unbounded.
		3.  Finally, accelerate to binary search to find the corner.
		'''
		max_corner = counterexample.copy()
		min_corner = counterexample.copy()
		self.no_upper_bound = []
		for i in range (0,len(self.variables)):
			self.no_upper_bound.append(False)
		self.no_lower_bound = []
		for i in range (0,len(self.variables)):
			self.no_lower_bound.append(False)
			
		for i in range(0,len(self.variables)):
			is_max_corner_found = False
			is_min_corner_found = False
			counter = 0
			while (not(is_max_corner_found and is_min_corner_found))  and counter < cutoff_value:
				counter += 1
				# do subset query with modified corner, if subset is false then we already had corner
				#print(max_corner, min_corner)
				if is_max_corner_found:
					pass
				else:
					start_point = self.build_lower_corner(min_corner)
					max_corner[i] = max_corner[i] + 1
					if i == 0:
						is_max_corner_found = not teacher.membership_query(self.build_point_formula(max_corner))
						if is_max_corner_found:
							max_corner[i] = max_corner[i] -1
					else:
						
						cube_formula = And(start_point, self.build_upper_corner(max_corner))	
						is_max_corner_found = not teacher.subset_query(cube_formula)
						#print("is max_corner found?: ",  is_max_corner_found, max_corner)
						if is_max_corner_found:
							max_corner[i] = max_corner[i] -1
				if is_min_corner_found:
					pass
				else:
					start_point_1 = self.build_upper_corner(max_corner)
					min_corner[i] = min_corner[i] - 1
					if i == 0:
						
						is_min_corner_found = not teacher.membership_query(self.build_point_formula(min_corner))
						#print(is_min_corner_found)
						if is_min_corner_found:
							min_corner[i] = min_corner[i] +1
					else:
						cube_formula = And(start_point_1, self.build_lower_corner(min_corner))	
						is_min_corner_found = not teacher.subset_query(cube_formula)
						#print("is min_corner found?: ",  is_min_corner_found, min_corner)
						if is_min_corner_found:
							min_corner[i] = min_corner[i] +1	
			# leaving while loop
			if not(is_max_corner_found):
				self.no_upper_bound[i] = True
				cube_formula = And(self.build_lower_corner(min_corner), self.build_upper_corner(max_corner))
				is_max_corner_found = teacher.subset_query(cube_formula)
				if not is_max_corner_found:
					self.no_upper_bound[i] = False
					
			
			
			lower_bound = max_corner.copy()
			upper_bound = min_corner.copy()
			if not(is_max_corner_found):
				stepsize = 1
				is_upper_bound = False
				
				while not (is_upper_bound):
					max_corner[i] = max_corner[i] + stepsize
					cube_formula = And(self.build_lower_corner(min_corner), self.build_upper_corner(max_corner))
					is_upper_bound = not teacher.subset_query(cube_formula)
					stepsize = stepsize * 2
				stepsize = int(stepsize / 2)
				lower_bound[i] = max_corner[i] - stepsize
				max_corner = self.binary_search(lower_bound, max_corner, i, teacher, self.build_lower_corner(min_corner))
				
			if not(is_min_corner_found):	
				self.no_lower_bound[i] = True
				cube_formula = And(self.build_upper_corner(max_corner), self.build_lower_corner(min_corner))
				is_min_corner_found = teacher.subset_query(cube_formula)
				if not is_min_corner_found:
					self.no_lower_bound[i] = False				
				
			if not(is_min_corner_found):
				stepsize = 1
				is_lower_bound = False
				while not (is_lower_bound):
					min_corner[i] = min_corner[i] - stepsize
					cube_formula = And(self.build_upper_corner(max_corner), self.build_lower_corner(min_corner))
					is_lower_bound = not teacher.subset_query(cube_formula)
					stepsize = stepsize * 2
				stepsize = stepsize / 2
				upper_bound[i] = min_corner[i] + stepsize
				min_corner = self.binary_search(min_corner, upper_bound, i, teacher, self.build_upper_corner(max_corner), max = False)
		return And(self.build_lower_corner(min_corner),self.build_upper_corner(max_corner))		
	
	
		
	def build_hypothesis(self):
		self.hypothesis = False
		for cube_formula in self.max_cubes:
			self.hypothesis = Or(self.hypothesis, cube_formula)
		return self.hypothesis
		
	def build_lower_corner(self,point):
		result = True
		for i in range(0,len(self.variables)):
			if self.no_lower_bound[i]:
				pass
			else:
				result =   And(result, point[i] <= self.variables[i])
		return result
	
	def build_upper_corner(self,point):
		result = True
		for i in range(0,len(point)):
			if self.no_upper_bound[i]:
				pass
			else:
				result = And(result, self.variables[i] <= point[i])
		return result

class Learner_trial_and_overshoot:
	def __init__(self, variables, unary = True, binary = False):
		self.max_cubes = []
		self.variables = variables
		self.counterexamples = []
		self.visited = []
		self.hypothesis = False
		self.solver = z3.Solver()
		self.unary = unary
		self.binary = binary
	
	def build_point_formula(self, point):
		formula = True
		for coordinate in range(0,len(point)):
			formula = And(formula, point[coordinate] == self.variables[coordinate])
		return formula
	
	def find_corner_unary(self, counterexample, teacher, max = True):
		max_corner = counterexample.copy()
		if max == True:
			for i in range (0,len(self.variables)):
				is_corner_found = False
				while is_corner_found == False:
					max_corner[i] = max_corner[i] +1
					is_corner_found = not teacher.membership_query(self.build_point_formula(max_corner))
				max_corner[i] = max_corner[i] -1
			return max_corner
		else: 
			for i in range (0,len(self.variables)):
				is_corner_found = False
				while is_corner_found == False:
					max_corner[i] = max_corner[i] -1
					is_corner_found = not teacher.membership_query(self.build_point_formula(max_corner))
				max_corner[i] = max_corner[i] +1
			return max_corner		
	
	def find_max_corner_binary(self, counterexample, teacher):
		'''
		First need to find a max from where we want to start off
		the minimum is the last positive membership query point
		Then apply binary search 
		'''
		max_corner = counterexample.copy()
		lower_bound = counterexample.copy()
		for i in range (0,len(self.variables)):
			is_upper_bound = False
			stepsize = 1
			while not is_upper_bound:
				max_corner[i] = max_corner[i] + stepsize
				
				is_upper_bound = not teacher.membership_query(self.build_point_formula(max_corner))
				stepsize = stepsize * 2
			stepsize = int(stepsize / 2)			
			lower_bound[i] = max_corner[i] - stepsize
			mid_point = lower_bound.copy()
			while lower_bound[i] != max_corner[i]:
				mid_point[i] = math.ceil((lower_bound[i] + max_corner[i]) /2)
				is_member = teacher.membership_query(self.build_point_formula(mid_point))
				mid_point[i] = ((lower_bound[i] + max_corner[i]) /2)
				if is_member:
					lower_bound[i] = math.ceil(mid_point[i])
					mid_point[i] = math.ceil(mid_point[i])
				else:
					max_corner[i] = math.floor(mid_point[i])
					mid_point[i] = math.floor(mid_point[i])
		return mid_point
			
	def find_min_corner_binary(self, counterexample, teacher):
		'''
		First need to find a max from where we want to start off
		the minimum is the last positive membership query point
		Then apply binary search 
		'''
		min_corner = counterexample.copy()
		upper_bound = counterexample.copy()
		for i in range (0,len(self.variables)):
			is_lower_bound = False
			stepsize = 1
			while not is_lower_bound:
				min_corner[i] = min_corner[i] - stepsize
				
				is_lower_bound = not teacher.membership_query(self.build_point_formula(min_corner))
				stepsize = stepsize * 2
			stepsize = int(stepsize / 2)			
			upper_bound[i] = min_corner[i] + stepsize
			mid_point = upper_bound.copy()
			while upper_bound[i] != min_corner[i]:
				mid_point[i] = math.floor((upper_bound[i] + min_corner[i]) /2)
				is_member = teacher.membership_query(self.build_point_formula(mid_point))
				mid_point[i] = ((upper_bound[i] + min_corner[i]) /2)
				if is_member:
					upper_bound[i] = math.floor(mid_point[i])
					mid_point[i] = math.floor(mid_point[i])
				else:
					min_corner[i] = math.ceil(mid_point[i])
					mid_point[i] = math.ceil(mid_point[i])
		return mid_point			
			
			
		if max == True:
			for i in range (0,len(self.variables)):
				is_corner_found = False
				while is_corner_found == False:
					max_corner[i] = max_corner[i] +1
					is_corner_found = not teacher.membership_query(self.build_point_formula(max_corner))
				max_corner[i] = max_corner[i] -1
			return max_corner
		else: 
			for i in range (0,len(self.variables)):
				is_corner_found = False
				while is_corner_found == False:
					max_corner[i] = max_corner[i] -1
					is_corner_found = not teacher.membership_query(self.build_point_formula(max_corner))
				max_corner[i] = max_corner[i] +1
			return max_corner		
	
	def binary_search(low_point, high_point, i, teacher):
		mid_point = low_point.copy()
		while low_point[i] != high_point[i]:
			mid_point[i] = (low_point[i] + high_point[i]) /2
			is_sub_set = teacher.membership_query(mid_point[i])
			if is_in_target:
				low_point[i] = math.ceil(mid_point[i])
			else:
				high_point[i] = math.floor(mid_point[i])
		return mid_point	
				
	def learn(self, teacher, target):
		is_hypothesis_correct = False
		while (not is_hypothesis_correct):
			teacher_reply = teacher.equivalence_query(self.hypothesis)
			is_hypothesis_correct = teacher_reply[0]
			counterexample = (teacher_reply[1])
			if (teacher_reply[1] == False):
				pass
			else: 
				# exclude the area of already visited points
				search_space = z3.Xor(self.hypothesis, target)
				if self.unary:
					min_point = self.find_corner_unary(counterexample, Teacher(self.variables,search_space), max = False)
				elif self.binary:
					min_point = self.find_min_corner_binary(counterexample, Teacher(self.variables,search_space))
				else:
					print("ERROR")
				for v_point in self.visited:
					for var in range(0,len(self.variables)):
						if int(v_point[var]) < int(min_point[var]):
							break
						else: 
							exclude = True
							for var in range(0,len(self.variables)):
								exclude = And(exclude, var >= v_point[var])
                                
							search_space = And(search_space, z3.Not(exclude))
				if self.unary:
					max_point = self.find_corner_unary(counterexample, Teacher(self.variables,search_space))
				elif self.binary:
					max_point = self.find_max_corner_binary(counterexample, Teacher(self.variables,search_space))
				else:
					print("ERROR")
				self.visited.append(min_point)
				cube = Cube(min_point, max_point, self.variables)
				self.hypothesis = z3.Xor(self.hypothesis, cube.get_cube_formula())
				self.solver.reset()
				self.solver.add(z3.Xor(self.hypothesis, target))
				is_hypothesis_correct = not (self.solver.check() == z3.sat)
		return self.hypothesis
	



'''
Class framework ensures the communication between the teacher and the 
learner
'''

class Max_cube_learning_framework:
	def __init__(self,variables):
		self.variables = variables
		self.learner = Learner(variables)
		self.teacher = Teacher(variables)
	
	def run(self):
		pass


	
def test1(max_cube = True, u = True, b = False, o = False):
	# 3 small cubes
	x = Int('x')
	y = Int('y')
	var = [x,y]	
	l1 = [0,0]
	l2 = [3,3]
	l3 = [1,1]
	l4 = [4,4]
	l5 = [2,2]
	l6 = [5,5]
	c1 = Cube(l1,l2,var)
	c2 = Cube(l3,l4,var)
	c3 = Cube(l5,l6,var)
	target = Or(c1.get_cube_formula(),Or(c2.get_cube_formula(),c3.get_cube_formula()))
	teacher = Teacher(var,target)
	start = time.time()
	if max_cube:
		learner = Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)
	
	
	end = time.time()
	print("Total time needed: ", end - start)
	if max_cube:
		print("Length: ", len(result))
		result_m_c = False
		for cube_formula in result:
			result_m_c = Or(result_m_c, cube_formula)
			#print("Formula: ", cube_formula, "\n")
		prove(result_m_c == target)
		return result_m_c
	prove(result == target)
	return result
	
def test2_and(k,max_cube = True, u = True, b = False, o = False):
	x = Int('x')
	y = Int('y')
	var = [x,y]	
	target = Or([And(x <= i+2,x >= i,y >= i,y <= i+2) for i in range(1,k)])
	target = And(target, x + y <= k)
	print(target)
	#target = Or(target, And(x + y == k, And(x >= 0, y >= 0)))	
	teacher = Teacher(var,target)
	start = time.time()
	if max_cube:
		learner = Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)
	
	
	end = time.time()
	print("Total time needed: ", end - start)
	if max_cube:
		print("Length: ", len(result))
		result_m_c = False
		for cube_formula in result:
			result_m_c = Or(result_m_c, cube_formula)
			print("Formula: ", cube_formula, "\n")
		prove(result_m_c == target)
		return result_m_c
	prove(result == target)
	return result
	
def test2_or(k,max_cube = True, u = True, b = False, o = False):
	x = Int('x')
	y = Int('y')
	var = [x,y]	
	target = Or([And(x <= i+2,x >= i,y >= i,y <= i+2) for i in range(1,k)])
	#target = And(target, x + y <= k)
	target = Or(target, And(x + y == k, And(x >= 0, y >= 0)))	
	teacher = Teacher(var,target)
	start = time.time()
	if max_cube:
		learner = Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)
	
	
	end = time.time()
	print("Total time needed: ", end - start)
	if max_cube:
		print("Length: ", len(result))
		result_m_c = False
		for cube_formula in result:
			result_m_c = Or(result_m_c, cube_formula)
			#print("Formula: ", cube_formula, "\n")
		prove(result_m_c == target)
		return result_m_c
	prove(result == target)
	return result
	
def test2_3d(k,max_cube = True, u = True, b = False, o = False):
	x = Int('x')
	y = Int('y')
	z = Int('z')
	var = [x,y,z]	
	target = Or([And(x <= i+2,x >= i,y >= i,y <= i+2, z <= i+2, z >=i) for i in range(1,k)])
	#target = And(target, x + y <= k)
	teacher = Teacher(var,target)
	start = time.time()
	if max_cube:
		learner = Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)
	
	
	end = time.time()
	print("Total time needed: ", end - start)
	if max_cube:
		print("Length: ", len(result))
		result_m_c = False
		for cube_formula in result:
			result_m_c = Or(result_m_c, cube_formula)
			#print("Formula: ", cube_formula, "\n")
		prove(result_m_c == target)
		return result_m_c
	prove(result == target)
	return result	

def test2_4d(k,max_cube = True, u = True, b = False, o = False):
	x = Int('x')
	y = Int('y')
	z = Int('z')
	a = Int('a')
	var = [x,y,z]	
	target = Or([And(x <= i+2,x >= i,y >= i,y <= i+2, z <= i+2, z >=i, a <= i+2, a >= i) for i in range(1,k)])
	#target = And(target, x + y <= k)
	teacher = Teacher(var,target)
	start = time.time()
	if max_cube:
		learner = Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)
	
	
	end = time.time()
	print("Total time needed: ", end - start)
	if max_cube:
		print("Length: ", len(result))
		result_m_c = False
		for cube_formula in result:
			result_m_c = Or(result_m_c, cube_formula)
			#print("Formula: ", cube_formula, "\n")
		prove(result_m_c == target)
		return result_m_c
	prove(result == target)
	return result

def test2_k_d(k, p,max_cube = True, u = True, b = False, o = False):
	# k variables, dimension k
	var = []
	for i in range (0,k):
		placeholder = Int(i)
		var.append(placeholder)
	target = False
	# p cubes, l = 1...p
	for l in range (1,p):
		temp_target = True
		for v in range(0,len(var)):
			temp_target = And(temp_target, var[v] <= l +2, var[v] >= l)
		target = Or(target, temp_target)
		
	teacher = Teacher(var,target)
	start = time.time()
	if max_cube:
		learner = Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)
	
	
	end = time.time()
	print("Total time needed: ", end - start)
	if max_cube:
		#print("Length: ", len(result))
		result_m_c = False
		for cube_formula in result:
			result_m_c = Or(result_m_c, cube_formula)
			#print("Formula: ", cube_formula, "\n")
		prove(result_m_c == target)
		#print(result_m_c)
		return result_m_c
	prove(result == target)
	return result

def test3(k, max_cube = True, u = True, b = False, o = False):
	# one big cube
	x = Int('x')
	y = Int('y')
	var = [x,y]
	l1 = [0,0]
	l2 = [k,k]
	c1 = Cube(l1,l2,var)
	target = c1.get_cube_formula()
	
	teacher = Teacher(var, target)
	start = time.time()
	if max_cube:
		learner =Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)			
	end = time.time()
	print("Total time needed: ", end - start)
	if max_cube:
		print("Length: ", len(result))
		result_m_c = False
		for cube_formula in result:
			result_m_c = Or(result_m_c, cube_formula)
			#print("Formula: ", cube_formula, "\n")
		prove(result_m_c == target)
		return result_m_c
	prove(result == target)
	return result
	
	
def test4(k, max_cube = True, u = True, b = False, o = False):
	# 100 big cubes, actually 99 big cubes
	x = Int('x')
	y = Int('y')
	var = [x,y]
	target = Or([And(x <= i+100,x >= i,y >= i,y <= i+100) for i in range(1,k)])
	teacher = Teacher(var, target)
	start = time.time()
	if max_cube:
		learner = Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)			
	end = time.time()
	print("Total time needed: ", end - start)
	if max_cube:
		print("Length: ", len(result))
		result_m_c = False
		for cube_formula in result:
			result_m_c = Or(result_m_c, cube_formula)
			#print("Formula: ", cube_formula, "\n")
		prove(result_m_c == target)
		return result_m_c
	prove(result == target)
	return result

def test1_unbounded():
	x = Int('x')
	y = Int('y')
	var = [x,y]
	target = True
	teacher = Teacher(var, target)
	start = time.time()
	learner = Learner_max_cubes(var, unary = False, binary = False, optimized = True)
	result = learner.learn(teacher)	
	end = time.time()
	print("Total time needed: ", end - start)
	print("Length: ", len(result))
	result_m_c = False
	for cube_formula in result:
		result_m_c = Or(result_m_c, cube_formula)
		#print("Formula: ", cube_formula, "\n")
	prove(result_m_c == target)
	return result_m_c
	
def test2_unbounded():
	x = Int('x')
	y = Int('y')
	var = [x,y]
	target = And(x >=0, y >= 0) 
	teacher = Teacher(var, target)
	start = time.time()
	learner = Learner_max_cubes(var, unary = False, binary = False, optimized = True)
	result = learner.learn(teacher)	
	end = time.time()
	print("Total time needed: ", end - start)
	print("Length: ", len(result))
	result_m_c = False
	for cube_formula in result:
		result_m_c = Or(result_m_c, cube_formula)
		#print("Formula: ", cube_formula, "\n")
	prove(result_m_c == target)
	return result_m_c	

def test3_unbounded(k):
	x = Int('x')
	y = Int('y')
	var = [x,y]
	l1 = [0,0]
	l2 = [k,k]
	c1 = Cube(l1,l2,var)
	target = c1.get_cube_formula()	
	target = Or(target,And(x <=0, y <= 0)) 
	teacher = Teacher(var, target)
	
	start = time.time()
	learner = Learner_max_cubes(var, unary = False, binary = False, optimized = True)
	result = learner.learn(teacher)	
	end = time.time()
	print("Total time needed: ", end - start)
	print("Length: ", len(result))
	result_m_c = False
	for cube_formula in result:
		result_m_c = Or(result_m_c, cube_formula)
		#print("Formula: ", cube_formula, "\n")
	prove(result_m_c == target)
	return result_m_c

def test4_unbounded(k):
	x = Int('x')
	y = Int('y')
	var = [x,y]
	target = Or([And(x <= i+2,x >= i,y >= i,y <= i+2) for i in range(1,k)])
	target = And(target, x + y <= k)	
	target = Or(target,And(x <=0, y <= 0)) 	
	teacher = Teacher(var, target)
	
	start = time.time()
	learner = Learner_max_cubes(var, unary = False, binary = False, optimized = True)
	result = learner.learn(teacher)	
	end = time.time()
	print("Total time needed: ", end - start)
	print("Length: ", len(result))
	result_m_c = False
	for cube_formula in result:
		result_m_c = Or(result_m_c, cube_formula)
		#print("Formula: ", cube_formula, "\n")
	prove(result_m_c == target)
	return result_m_c

def test5_unbounded(k):
	x = Int('x')
	y = Int('y')
	var = [x,y]
	target = Or([And(x >= i,y >= -i) for i in range(0,k)])
	#target = Or(target, And(x + y == k, And(x >= 0, y >= 0)))
	teacher = Teacher(var, target)	
	start = time.time()
	learner = Learner_max_cubes(var, unary = False, binary = False, optimized = True)
	result = learner.learn(teacher)	
	end = time.time()
	print("Total time needed: ", end - start)
	print("Length: ", len(result))
	result_m_c = False
	for cube_formula in result:
		result_m_c = Or(result_m_c, cube_formula)
		#print("Formula: ", cube_formula, "\n")
	prove(result_m_c == target)
	return result_m_c

def test_scale(k):
	print("\n Overshoot Solver unary and:", k ,", \n")
	test2_and(k, max_cube = False)
	print("\n Max Cube Solver unary and:", k ," \n")
	test2_and(k)
	print("\n Overshoot Solver binary and:", k, ", \n")
	test2_and(k, max_cube = False, u = False, b = True)
	print("\n Max Cube Solver binary and:", k ," \n")
	test2_and(k, u = False, b = True)
	print("\n Max Cube Solver opt and:", k, " \n")
	test2_and(k, u = False, b = False, o = True)

def test_scale_or(k):
	print("\n Overshoot Solver unary and:", k ,", \n")
	#test2_or(k, max_cube = False)
	print("\n Max Cube Solver unary and:", k ," \n")
	test2_or(k)
	print("\n Overshoot Solver binary and:", k, ", \n")
	#test2_or(k, max_cube = False, u = False, b = True)
	print("\n Max Cube Solver binary and:", k ," \n")
	test2_or(k, u = False, b = True)
	print("\n Max Cube Solver opt and:", k, " \n")
	test2_or(k, u = False, b = False, o = True)
	
def test_scale_big(k):
	print("\n Overshoot Solver unary and:", k ,", \n")
	test4(k, max_cube = False)
	print("\n Max Cube Solver unary and:", k ," \n")
	#test4(k)
	print("\n Overshoot Solver binary and:", k, ", \n")
	#test4(k, max_cube = False, u = False, b = True)
	print("\n Max Cube Solver binary and:", k ," \n")
	test4(k, u = False, b = True)
	print("\n Max Cube Solver opt and:", k, " \n")
	test4(k, u = False, b = False, o = True)	
	
def test_max_cube_unary():
	print("\n Max Cube Solver Test 1: \n")
	test1()
	print("\n Max Cube Solver Test 2 and: \n")
	test2_and(5)
	print("\n Max Cube Solver Test 3 or: \n")
	test2_or(5)
	print("\n Max Cube Solver Test 4: \n")
	test3(10)
	print("\n Max Cube Solver Test 5: \n")
	test4(1000)
	
def test_max_cube_binary():
	print("\n Max Cube Solver Test 1 binary: \n")
	test1(u = False, b = True)
	print("\n Max Cube Solver Test 2 and binary: \n")
	test2_and(5,u = False, b = True)
	print("\n Max Cube Solver Test 3 or binary: \n")
	test2_or(500, u = False, b = True)
	print("\n Max Cube Solver Test 4 binary: \n")
	test3(1, u = False, b = True)
	print("\n Max Cube Solver Test 5 binary: \n")
	test4(1, u = False, b = True)
	
def test_max_cube_optimized():
	print("\n Max Cube Solver Test 1 op: \n")
	test1(u = False, b = False, o = True)
	print("\n Max Cube Solver Test 2 and op: \n")
	test2_and(500,u = False, b = False, o = True)
	print("\n Max Cube Solver Test 2 or op: \n")
	test2_or(500, u = False, b = False, o = True)
	print("\n Max Cube Solver Test 3 op: \n")
	test3(1000, u = False, b = False, o = True)
	print("\n Max Cube Solver Test 4 op: \n")
	test4(1000, u = False, b = False, o = True)

def test_max_cube_optimized_unbounded():
	print("\n Max Cube Solver Test 1 unbounded op: \n")
	test1_unbounded()
	print("\n Max Cube Solver Test 2 unbounded op: \n")
	test2_unbounded()
	print("\n Max Cube Solver Test 3 unbounded op: \n")
	test3_unbounded(1000)
	print("\n Max Cube Solver Test 4 unbounded op: \n")
	test4_unbounded(50)
	print("\n Max Cube Solver Test 5 unbounded op: \n")
	test5_unbounded(500)
	
def test_boolean_1(max_cube = True, u = True, b = False, o = False):
	var = []
	for i in range (0,8):
		placeholder = Int(i)
		var.append(placeholder)
	target = 1 == land(land(land(land(land(land(land(land(land(lor(var[0],var[1]),lor(var[2],var[3])),lor(var[4],var[5])),lor(var[6],var[7])),lor(var[0],var[6])),lor(var[0],var[2])),lor(var[0],var[3])),lor(var[0],var[4])),lor(var[0],var[5])),lor(var[0],var[7]))
	for i in range(0,8):
		target = And(target, var[i] >=0)
		target = And(target, var[i] <=1)
	teacher = Teacher(var, target)
	
	start = time.time()
	if max_cube:
		learner = Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)	
	end = time.time()
	print("Total time needed: ", end - start)
	return result

def test_boolean_2(max_cube = True, u = True, b = False, o = False):
	var = []
	for i in range (0,18):
		placeholder = Int(i)
		var.append(placeholder)
	target = 1 == land(land(land(land(land(land(land(land(land(lor(var[0],lor(var[1],var[8])),lor(var[2],lor(var[3],var[9]))),lor(var[4],lor(var[5],var[10]))),lor(var[6],lor(var[7],var[11]))),lor(var[0],lor(var[6],var[12]))),lor(var[0],lor(var[2],var[13]))),lor(var[0],lor(var[3],var[14]))),lor(var[0],lor(var[4],var[15]))),lor(var[0],lor(var[5],var[16]))),lor(var[0],lor(var[7],var[17])))
	for i in range(0,18):
		target = And(target, var[i] >=0)
		target = And(target, var[i] <=1)
	teacher = Teacher(var, target)
	
	start = time.time()
	if max_cube:
		learner = Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)	
	end = time.time()
	print("Total time needed: ", end - start)
	return result


def ip01_1(max_cube = True, u = True, b = False, o = False):
	var = []
	a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14 = Consts('x9_plus x9_minus x7_plus x7_minus x5_plus x5_minus x4_plus 4', IntSort())
	for i in range(0,18):
		target = And(target, var[i] >=0)
		target = And(target, var[i] <=1)
	teacher = Teacher(var, target)
	
	start = time.time()
	if max_cube:
		learner = Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)	
	end = time.time()
	print("Total time needed: ", end - start)
	return result

def cav2009_10vars(smt2file, lower_limit, upper_limit):
	x0, x1, x2, x3, x4, x5, x6, x7, x8, x9  = Ints('x0 x1 x2 x3 x4 x5 x6 x7 x8 x9')
	var = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9]
	target_vector = parse_smt2_file("b1.smt2")
	# add lower and upper limit for the variables to make sure it is mondec
	
	# iterate the vector and from it into an and formula
	target = True
	for v in var:
		target = And(target, v >= lower_limit, v <= upper_limit)
	for formula in target_vector:
		target = And(target, formula)
		print(formula)
	teacher = Teacher(var, target)
	start = time.time()
	if max_cube:
		print("test1")
		learner = Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		print("test2")
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)	
	end = time.time()
	print("Total time needed: ", end - start)
	return result

def cindy(max_cube = True, u = False, b = False, o = True):
	b1,b2,b3,b4,b5,r  = Ints('b1 b2 b3 b4 b5 r')
	var = [b1,b2,b3,b4,b5,r]
	target = Or(And(b1 <= 20, b2 <= 20, b3 <= 10, b4 <= 10, b5 <= 0, r == 1), And(b1 <= 20, b2 <= 20, b3 <= 0, b4 <= 10, b5 <= 10, r ==1), And(b1 <= 10, b2 <= 20, b3 <= 20, b4 <= 0, b5<= 10, r == 2),And(b1 <= 0, b2 <= 20, b3 <= 20, b4 <= 10, b5 <= 10, r== 2), And(b1 <= 10, b2 <= 0, b3 <= 20, b4 <= 20, b5 <= 10, r == 3), And(b1 <= 10, b2 <= 10, b3 <= 20, b4 <= 20, b5 <= 10, r == 3), And(b1 <= 0, b2 <= 10, b3 <= 10, b4 <= 20, b5 <= 20, r == 4), And(b1 <= 10, b2<= 10, b3<= 0, b4 <= 20, b5 <= 20, r == 4), And(b1 <= 20, b2 <= 10, b3 <= 10, b4 <= 0, b5 <= 20, r == 5), And(b1 <= 20, b2 <= 0, b3 <= 10, b4 <= 10, b5 <= 20, r == 5), And(b1 >= 0, b2 >= 0, b3 >= 0, b4 >= 0, b5 >=0))
	teacher = Teacher(var, target)
	start = time.time()
	if max_cube:
		learner = Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)			
	end = time.time()	
	print("Total time needed: ", end - start)

def mondec1(k, max_cube = True, u = False, b = False, o = True):
	print(max_cube,u,b,o)
	x,y  = Ints('x y')
	var = [x,y]
	target = Implies(And(0 <= x, x <= k),And(0 <= y, x +y <=k))
	teacher = Teacher(var, target)
	start = time.time()
	if max_cube:
		learner = Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)			
	end = time.time()	
	print("Total time needed: ", end - start)

def cindy300c(max_cube = True, u = False, b = False, o = True):
	b1,b2,b3,b4,b5,r  = Ints('b1 b2 b3 b4 b5 r')
	var = [b1,b2,b3,b4,b5,r]
	target = Or(And(b1 <= 200, b2 <= 200, b3 <= 100, b4 <= 100, b5 <= 0, r == 1), And(b1 <= 200, b2 <= 200, b3 <= 0, b4 <= 100, b5 <= 100, r ==1), And(b1 <= 100, b2 <= 200, b3 <= 200, b4 <= 0, b5<= 100, r == 2),And(b1 <= 0, b2 <= 200, b3 <= 200, b4 <= 100, b5 <= 100, r== 2), And(b1 <= 100, b2 <= 0, b3 <= 200, b4 <= 200, b5 <= 100, r == 3), And(b1 <= 100, b2 <= 100, b3 <= 200, b4 <= 200, b5 <= 100, r == 3), And(b1 <= 0, b2 <= 100, b3 <= 100, b4 <= 200, b5 <= 200, r == 4), And(b1 <= 100, b2<= 100, b3<= 0, b4 <= 200, b5 <= 200, r == 4), And(b1 <= 200, b2 <= 100, b3 <= 100, b4 <= 0, b5 <= 200, r == 5), And(b1 <= 200, b2 <= 0, b3 <= 100, b4 <= 100, b5 <= 200, r == 5), And(b1 >= 0, b2 >= 0, b3 >= 0, b4 >= 0, b5 >=0))
	teacher = Teacher(var, target)
	start = time.time()
	if max_cube:
		learner = Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)			
	end = time.time()	
	print("Total time needed: ", end - start)

def cindy6b(max_cube = True, u = False, b = False, o = True):
	b1,b2,b3,b4,b5,b6,r  = Ints('b1 b2 b3 b4 b5 b6 r')
	var = [b1,b2,b3,b4,b5,b6,r]
	target = Or(And(b1 <= 20, b2 <= 20, b3 <= 10, b4 <= 10, b5 <= 0, b6 <= 0, r == 1),And(b1 <= 10, b2 <= 10, b3 <= 0, b4 <= 0, b5 <= 20, b6 <= 20, r == 5),And(b1 <= 0, b2 <= 0, b3 <= 20, b4 <= 20, b5 <= 10, b6 <= 10, r == 3), And(b1 <= 20, b2 <= 20, b3 <= 0, b4 <= 0, b5 <= 10, b6 <= 10, r ==1), And(b1 <= 10, b2 <= 20, b3 <= 20, b4 <= 0, b5<= 10, b6 <= 10, r == 2),And(b1 <= 0, b2 <= 20, b3 <= 20, b4 <= 10, b5 <= 10, b6 <= 10, r== 2), And(b1 <= 10, b2 <= 0, b3 <= 20, b4 <= 20, b5 <= 10, b6 <= 10, r == 3), And(b1 <= 10, b2 <= 10, b3 <= 20, b4 <= 20, b5 <= 10, b6 <= 10, r == 3), And(b1 <= 0, b2 <= 10, b3 <= 10, b4 <= 20, b5 <= 20, b6 <= 0, r == 4), And(b1 <= 10, b2<= 10, b3<= 0, b4 <= 20, b5 <= 20, b6 <= 0, r == 4), And(b1 <= 0, b2 <= 10, b3 <= 10, b4 <= 0, b5 <= 20, b6 <= 20, r == 5), And(b1 <= 0, b2 <= 0, b3 <= 10, b4 <= 10, b5 <= 20, b6 <= 20, r == 5), And(b1 >= 0, b2 >= 0, b3 >= 0, b4 >= 0, b5 >=0, b6 >= 0))
	teacher = Teacher(var, target)
	start = time.time()
	if max_cube:
		learner = Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)			
	end = time.time()	
	print("Total time needed: ", end - start)

def cindy6b300c(max_cube = True, u = False, b = False, o = True):
	b1,b2,b3,b4,b5,b6,r  = Ints('b1 b2 b3 b4 b5 b6 r')
	var = [b1,b2,b3,b4,b5,b6,r]
	target = Or(And(b1 <= 200, b2 <= 200, b3 <= 100, b4 <= 100, b5 <= 0, b6 <= 0, r == 1),And(b1 <= 100, b2 <= 100, b3 <= 0, b4 <= 0, b5 <= 200, b6 <= 200, r == 5),And(b1 <= 0, b2 <= 0, b3 <= 200, b4 <= 200, b5 <= 100, b6 <= 100, r == 3), And(b1 <= 200, b2 <= 200, b3 <= 0, b4 <= 0, b5 <= 100, b6 <= 100, r ==1), And(b1 <= 100, b2 <= 200, b3 <= 200, b4 <= 0, b5<= 100, b6 <= 100, r == 2),And(b1 <= 0, b2 <= 200, b3 <= 200, b4 <= 100, b5 <= 100, b6 <= 100, r== 2), And(b1 <= 10, b2 <= 0, b3 <= 200, b4 <= 200, b5 <= 100, b6 <= 100, r == 3), And(b1 <= 100, b2 <= 100, b3 <= 200, b4 <= 200, b5 <= 100, b6 <= 100, r == 3), And(b1 <= 0, b2 <= 100, b3 <= 100, b4 <= 200, b5 <= 200, b6 <= 0, r == 4), And(b1 <= 100, b2<= 100, b3<= 0, b4 <= 200, b5 <= 200, b6 <= 0, r == 4), And(b1 <= 0, b2 <= 100, b3 <= 100, b4 <= 0, b5 <= 200, b6 <= 200, r == 5), And(b1 <= 0, b2 <= 0, b3 <= 100, b4 <= 100, b5 <= 200, b6 <= 200, r == 5), And(b1 >= 0, b2 >= 0, b3 >= 0, b4 >= 0, b5 >=0, b6 >= 0))
	teacher = Teacher(var, target)
	start = time.time()
	if max_cube:
		learner = Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)			
	end = time.time()	
	print("Total time needed: ", end - start)

def cindy6b300cminw(max_cube = True, u = False, b = False, o = True):
	b1,b2,b3,b4,b5,b6,r  = Ints('b1 b2 b3 b4 b5 b6 r')
	var = [b1,b2,b3,b4,b5,b6,r]
	target = Or(And(b1 <= 200, b2 <= 200, b3 <= 100, b4 <= 100, b5 <= 0, b6 <= 0, r == 1),And(b1 <= 0, b2 <= 0, b3 <= 200, b4 <= 200, b5 <= 100, b6 <= 100, r == 3),And(b1 <= 100, b2 <= 100, b3 <= 0, b4 <= 0, b5 <= 200, b6 <= 200, r == 5))
	teacher = Teacher(var, target)
	start = time.time()
	if max_cube:
		learner = Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)			
	end = time.time()	
	print("Total time needed: ", end - start)
	
def control_unit(k, max_cube = True, u = False, b = False, o = True):
	var = []
	for i in range (0,k):
		placeholder = Int(i)
		var.append(placeholder)
	target = True
	for v in range(0, k-1):
		target = And(target, Or(And(1 <= var[v], var[v] <= 5, var[k-1]  == 0), And(2 <= var[v], var[v] <= 4, var[k-1]  == 1)))
	teacher = Teacher(var, target)
	start = time.time()
	if max_cube:
		learner = Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)			
	end = time.time()	
	print("Total time needed: ", end - start)
	

def	diagonal(k, max_cube = True, u = False, b = False, o = True):
	# one big cube
	x = Int('x')
	y = Int('y')
	var = [x,y]
	target = And(x == y, x >= 0, x <= k, y >= 0, y <= k)
	
	teacher = Teacher(var, target)
	start = time.time()
	if max_cube:
		learner =Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)			
	end = time.time()
	print("Total time needed: ", end - start)
	if max_cube:
		print("Length: ", len(result))
		result_m_c = False
		for cube_formula in result:
			result_m_c = Or(result_m_c, cube_formula)
			#print("Formula: ", cube_formula, "\n")
		prove(result_m_c == target)
		return result_m_c
	prove(result == target)
	return result	
	
def	diagonal_5d(k, max_cube = True, u = False, b = False, o = True):
	# one big cube
	
	x = Int('x')
	y = Int('y')
	var = [x,y]
	target = And(x == y, x >= 0, x <= 10000, y >= 0, y <= 10000)
	
	teacher = Teacher(var, target)
	start = time.time()
	if max_cube:
		learner =Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)			
	end = time.time()
	print("Total time needed: ", end - start)
	if max_cube:
		print("Length: ", len(result))
		result_m_c = False
		for cube_formula in result:
			result_m_c = Or(result_m_c, cube_formula)
			#print("Formula: ", cube_formula, "\n")
		prove(result_m_c == target)
		return result_m_c
	prove(result == target)
	return result

def mondec2(k, max_cube = True, u = False, b = False, o = True):
	x,y  = Ints('x y')
	var = [x,y]
	target = Implies(x >= 0,And( y >= 0, x +y >=k))
	teacher = Teacher(var, target)
	start = time.time()
	if max_cube:
		learner = Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)			
	end = time.time()	
	print("Total time needed: ", end - start)

def z3_abs(x):
	return If(x >=0, x, -x)
	
def lor(x,y):
	return If(x >=y, x, y)

def land(x,y):
	return If(x >=y, y, x)

def neg(x):
	return 1-x
	
if __name__ == '__main__':

	# arg1: name of the smt file or benchmark
	
	'''
	1. dia-r
	2. dia-u
	3. big-c
	4. k-cubes
	5. k-dia
	6. mondec
	'''
	# arg2: name of tool
	'''
	1. overshoot-u
	2. overshoot-b
	3. max-u
	4. max-b
	5. max-o
	
	'''
	# arg3 : parameter k for suites 1-4
	# arg4 : parameter d for suite 4
	
	print(sys.argv)
	m1 = False
	u1 = False
	b1 = False
	o1 = False
	if sys.argv[2] == "overshoot-u":
		u1 = True
	elif sys.argv[2] == "overshoot-b":
		b1 = True
	elif sys.argv[2] == "max-u":
		m1 = True
		u1 = True
	elif sys.argv[2] == "max-b":
		m1 = True
		b1 = True
	elif sys.argv[2] == "max-o":
		m1 = True
		o1 = True
	print(m1,u1,b1,o1)
	#all_tests = False
	
	if sys.argv[1] == "dia-r":
		print("\n Running test on diagonal restricted... \n", sys.argv[2], " Parameter k: ", sys.argv[3])
		test2_and(int(sys.argv[3]), max_cube = m1, u = u1, b = b1, o = o1)
	elif sys.argv[1] == "dia-u":
		print("\n Running test on diagonal unrestricted... \n", sys.argv[2], " Parameter k: ", sys.argv[3])
		test2_or(int(sys.argv[3]), max_cube = m1, u = u1, b = b1, o = o1)	
	elif sys.argv[1] == "big-c":
		print("\n Running test on big overlapping cube... \n", sys.argv[2], " Parameter k: ", sys.argv[3])
		test4(int(sys.argv[3]), max_cube = m1, u = u1, b = b1, o = o1)
	elif sys.argv[1] == "k-cubes":
		print("\n Running test on k overlapping cube... \n", sys.argv[2], " Parameter k: ", sys.argv[3], "Dimension d: ", sys.argv[4])
		test2_k_d(int(sys.argv[4]),int(sys.argv[3]), max_cube = m1, u = u1, b = b1, o = o1)
	elif sys.argv[1] == "k-dia":
		print("\n Running test on k diagonal... \n", sys.argv[2], " Parameter k: ", sys.argv[3])
		diagonal(int(sys.argv[3]), max_cube = m1, u = u1, b = b1, o = o1)
	elif sys.argv[1] == "mondec":
		print("\n Running test on mondec. WARNING: Will only terminate if max-o is chosen... \n", sys.argv[2], " Parameter k: ", sys.argv[3])
		mondec2(int(sys.argv[3]), max_cube = m1, u = u1, b = b1, o = o1)
	else:
		print("Command ", sys.argv[1], "  not recognized")
		
	'''if all_tests:
		print("\n Max Cube Solver Test 1: \n")
		result1 = test1()
		print("\n Trial and Overshoot Solver Test 1: \n")
		result2 = test1(max_cube = False)
		print("Sanity check do both Solvers produce the same result?:")
		prove(result1 == result2)
		print("\n Max Cube Solver Test 2: \n")
		result3 = test2_and(50)
		print("\n Trial and Overshoot Solver Test 2: \n")
		result4 = test2_and(50, max_cube = False)
		#print(result4)
		print("Sanity check do both Solvers produce the same result?:")
		prove(result3 == result4)
		
		print("\n Max Cube Solver Test 3 unary: \n")
		result5 = test3(1000, max_cube = True, u = True, b = False)
		print("\n Max Cube Solver Test 3 binary: \n")
		result6 = test3(1000, max_cube = True, u = False, b = True)
		
		print("\n Trial and Overshoot Solver Test 3 unary: \n")
		result5 = test3(1000, max_cube = False, u = True, b = False)
		print("\n Trial and Overshoot Solver Test 3 binary: \n")
		result6 = test3(1000, max_cube = False, u = False, b = True)
		print("\n Max Cube Solver Test 3 unary: \n")
		
		print("\n Max Cube Solver Test 4 unary: \n")	
		result5 = test4(1000, max_cube = True, u = True, b = False)
		print("\n Max Cube Solver Test 4 binary: \n")
		result6 = test4(1000, max_cube = True, u = False, b = True)
		
		print("\n Trial and Overshoot Solver Test 4 unary: \n")
		result5 = test4(1000, max_cube = False, u = True, b = False)
		print("\n Trial and Overshoot Solver Test 4 binary: \n")
		result6 = test4(1000, max_cube = False, u = False, b = True)'''
	

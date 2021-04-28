from maximal_cubes import *



def run_file(smt2file, var, max_cube = True, u = False, b = False, o = True):
	target_vector = parse_smt2_file(smt2file)
	# add lower and upper limit for the variables to make sure it is mondec
	
	# iterate the vector and from it into an and formula
	target = True
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

if __name__ == '__main__':

	
	print(sys.argv)
	smt2file = sys.argv[2]
	var_name = []
	var = []
	for i in range (0,len(sys.argv)):
		if i > 2:
			var_name.append(sys.argv[i])
	for i in range (0,len(var_name)):
		temp = Int(var_name[i])
		var.append(temp)
	
	print(var_name, var)
	m1 = False
	u1 = False
	b1 = False
	o1 = False
	if sys.argv[1] == "overshoot-u":
		u1 = True
	elif sys.argv[1] == "overshoot-b":
		b1 = True
	elif sys.argv[1] == "max-u":
		m1 = True
		u1 = True
	elif sys.argv[1] == "max-b":
		m1 = True
		b1 = True
	elif sys.argv[1] == "max-o":
		m1 = True
		o1 = True
	print(m1,u1,b1,o1)
	run_file(smt2file, var, max_cube = m1, u = u1, b = b1, o = o1)

from maximal_cubes import *
import mondec

def run_file(smt2file, max_cube = True, u = False, b = False, o = True, md=False):
	target_vector = parse_smt2_file(smt2file)
	
	# iterate the vector and from it build a AND formula
	target = True
	for formula in target_vector:
		target = And(target, formula)

	var = z3util.get_vars(formula)
	print("Variables: %r" % var)
	print("Formula: %r" % formula)

	def lambda_model(value):
		"""The mondec algorithm requires a lambda function as an input, instantiating
		the formula with any list of free variables.
		Note that substitue() may have an overhead (direct lambda specification
		may be faster)
		"""
		return substitute(formula, *((vname, value[i]) for (i, vname) in enumerate(var)))
	
	start = time.time()
	if md:
		result = mondec.mondec(lambda_model, var)
	elif max_cube:
		teacher = Teacher(var, target)
		learner = Learner_max_cubes(var, unary = u, binary = b, optimized = o)
		result = learner.learn(teacher)
	else:
		teacher = Teacher(var, target)
		learner = Learner_trial_and_overshoot(var, unary = u, binary = b)
		result = learner.learn(teacher,target)	
	end = time.time()
	print("Res: %r" % result)
	print("Total time needed: ", end - start)
	return result

if __name__ == '__main__':
	if len(sys.argv) < 3:
		print("Usage: %s [overshoot-u|overshoot-b|max-u|max-b|max-o|mondec] filename.smt2")
		sys.exit(0)

	smt2file = sys.argv[2]
	
	m1 = False
	u1 = False
	b1 = False
	o1 = False
	md = False
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
	elif sys.argv[1] == "mondec":
		md= True
	else:
		print("Unknown solver: %s" % sys.argv[1])
		sys.exit(1)
	run_file(smt2file, max_cube = m1, u = u1, b = b1, o = o1, md=md)

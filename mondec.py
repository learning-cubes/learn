from z3 import *
import time
def nu_ab(R, x, y, a, b):
    x_ = [ Const("x_%d" %i, x[i].sort()) for i in range(len(x))]
    y_ = [ Const("y_%d" %i, y[i].sort()) for i in range(len(y))]
    return Or(Exists(y_, R(x+y_) != R(a+y_)), Exists(x_, R(x_+y) != R(x_+b)))

def isUnsat(fml):
    s = Solver(); s.add(fml); return unsat == s.check()

def lastSat(s, m, fmls):
    if len(fmls) == 0: return m
    s.push(); s.add(fmls[0])
    if s.check() == sat: m = lastSat(s, s.model(), fmls[1:])       
    s.pop(); return m

def mondec(R, variables):
    #print(variables)
    phi = R(variables);  
    if len(variables)==1: return phi
    l = int(len(variables)/2)
    x, y = variables[0:l], variables[l:]
    def dec(nu, pi):
        if isUnsat(And(pi, phi)): 
           return BoolVal(False)
        if isUnsat(And(pi, Not(phi))): 
           return BoolVal(True)
        fmls = [BoolVal(True), phi, pi] 
        #try to extend nu
        m = lastSat(nu, None, fmls)              
        #nu must be consistent 
        assert(m != None)                         
        a = [ m.evaluate(z, True) for z in x ]
        b = [ m.evaluate(z, True) for z in y ]
        psi_ab = And(R(a+y), R(x+b))
        phi_a = mondec(lambda z: R(a+z), y)
        phi_b = mondec(lambda z: R(z+b), x)
        nu.push()
        #exclude: x~a and y~b
        nu.add(nu_ab(R, x, y, a, b))              
        t = dec(nu, And(pi, psi_ab)) 
        f = dec(nu, And(pi, Not(psi_ab)))
        nu.pop()
        return If(And(phi_a, phi_b), t, f)
    #nu is initially true
    return dec(Solver(), BoolVal(True))

def test_mondec(k):                             
    R = lambda v:And(v[1] > 0, (v[1] & (v[1] - 1)) == 0,
                     (v[0] & (v[1] % ((1 << k) - 1))) != 0)
    bvs = BitVecSort(2*k)                        #use 2k-bit bitvectors
    x, y = Consts('x y', bvs)
    res = mondec(R, [x, y])
    #assert(isUnsat(res != R([x, y])))             #check correctness 
    print("mondec1(", R([x, y]), ") =", res)

def test_mondec1(k):
    R = lambda v:And(v[0] + v[1] >= k,v[0] >= 0, v[1] >= 0)
    x, y = Consts('x y', IntSort())
    res = mondec(R, [x, y])
    #assert(isUnsat(res != R([x, y])))             #check correctness 
    print("mondec1(", R([x, y]), ") =", res)

def test_mondec2(k):
    R = lambda v:Or(Or([And(v[0] <= i+2,v[0] >= i,v[1] >= i,v[1] <= i+2) for
                        i in range(1,k)]),
                    And(v[0] + v[1] == k,v[0] >= 0, v[1] >= 0))
    x, y = Consts('x y', IntSort())
    res = mondec(R, [x, y])
    #assert(isUnsat(res != R([x, y])))             #check correctness 
    print("mondec1(", R([x, y]), ") =", res)
    
def test_mondec3(k):
    R = lambda v:Or([And(v[0] <= i+2,v[0] >= i,v[1] >= i,v[1] <= i+2) for
                        i in range(1,k)])
    x, y = Consts('x y', IntSort())
    res = mondec(R, [x, y])
    #assert(isUnsat(res != R([x, y])))             #check correctness 
    print("mondec1(", R([x, y]), ") =", res)


def test_mondec4(k):
    R = lambda v:Or([And(v[0] <= i+2,v[0] >= i,v[1] >= i,v[1] <= i+2) for
                        i in range(1,k)])
    x, y = Consts('x y', IntSort())
    res = mondec(R, [x, y])
    #assert(isUnsat(res != R([x, y])))             #check correctness 
    print("mondec1(", R([x, y]), ") =", res)
    
def test_mondec5(k):
    R = lambda v:And(And(v[0] <= 1000,v[0] >= 0,v[1] >= 0,v[1] <= 1000))
    x, y = Consts('x y', IntSort())
    res = mondec(R, [x, y])
    #assert(isUnsat(res != R([x, y])))             #check correctness 
    print("mondec1(", R([x, y]), ") =", res)
    
def test_mondec6(k):
    R = lambda v:Or([And(v[0] <= i+k,v[0] >= i,v[1] >= i,v[1] <= i+k) for
                        i in range(1,100)])
    x, y = Consts('x y', IntSort())
    res = mondec(R, [x, y])
    #assert(isUnsat(res != R([x, y])))             #check correctness 
    print("mondec1(", R([x, y]), ") =", res)

def test_mondec7():
    R = lambda v:True
    x, y = Consts('x y', IntSort())
    res = mondec(R, [x, y])
    #assert(isUnsat(res != R([x, y])))             #check correctness 
    print("mondec1(", R([x, y]), ") =", res)

def test_mondec8():
    R = lambda v:And(x >=0, y >= 0) 
    x, y = Consts('x y', IntSort())
    res = mondec(R, [x, y])
    #assert(isUnsat(res != R([x, y])))             #check correctness 
    print("mondec1(", R([x, y]), ") =", res)

def test_mondec9(k):
    R = lambda v:Or([And(v[0] <= i+100,v[0] >= i,v[1] >= i,v[1] <= i+100) for
                        i in range(1,k)])
    x, y = Consts('x y', IntSort())
    res = mondec(R, [x, y])
    #assert(isUnsat(res != R([x, y])))             #check correctness 
    print("mondec1(", R([x, y]), ") =", res)
    
def test_mondec10(k):
    R = lambda v:And(Or([And(v[0] <= i+2,v[0] >= i,v[1] >= i,v[1] <= i+2) for
                        i in range(1,k)]),
                    v[0] + v[1]<= k)
    x, y = Consts('x y', IntSort())
    res = mondec(R, [x, y])
    #assert(isUnsat(res != R([x, y])))             #check correctness 
    print("mondec1(", R([x, y]), ") =", res)

def test_mondec11(k):
    R = lambda v:Or([And(x >= i,y >= -i) for i in range(0,k)])
    x, y = Consts('x y', IntSort())
    res = mondec(R, [x, y])
    #assert(isUnsat(res != R([x, y])))             #check correctness 
    print("mondec1(", R([x, y]), ") =", res)

def test_mondec12(k):
    R = lambda v:Or(Or([And(x >= i,y >= -i) for i in range(0,k)]),And(x + y == k, And(x <= 0, y <= 0)))
    x, y = Consts('x y', IntSort())
    res = mondec(R, [x, y])
    #assert(isUnsat(res != R([x, y])))             #check correctness 
    print("mondec1(", R([x, y]), ") =", res)

def test_mondec13(k):
    R = lambda v:And(Or([And(v[0] <= i+2,v[0] >= i,v[1] >= i,v[1] <= i+2,v[2] >= i,v[2] <= i+2) for
                        i in range(1,k)]),
                    And(v[0] + v[1] + v[2] <= k))
    x, y, z = Consts('x y z', IntSort())
    res = mondec(R, [x, y, z])
    #assert(isUnsat(res != R([x, y, z])))             #check correctness 
    print("mondec1(", R([x, y, z]), ") =", res)

def test_mondec13_4(k):
    R = lambda v:And(Or([And(v[0] <= i+2,v[0] >= i,v[1] >= i,v[1] <= i+2,v[2] >= i,v[2] <= i+2,v[3] >= i,v[3] <= i+2) for
                        i in range(1,k)]),
                    And(v[0] + v[1] + v[2] + v[3]<= k))
    x, y, z, a = Consts('x y z a', IntSort())
    res = mondec(R, [x, y, z,a])
    #assert(isUnsat(res != R([x, y, z,a])))             #check correctness 
    print("mondec1(", R([x, y, z,a]), ") =", res)


def test_mondec13_5(k):
    R = lambda v:And(Or([And(v[0] <= i+2,v[0] >= i,v[1] >= i,v[1] <= i+2,v[2] >= i,v[2] <= i+2,v[3] >= i,v[3] <= i+2,v[4] >= i,v[4] <= i+2) for
                        i in range(1,k)]),
                    And(v[0] + v[1] + v[2] + v[3] + v[4]<= k))
    x, y, z, a,b= Consts('x y z a b', IntSort())
    res = mondec(R, [x, y, z,a,b])
    #assert(isUnsat(res != R([x, y, z,a,b])))             #check correctness 
    print("mondec1(", R([x, y, z,a,b]), ") =", res)

def test_mondec13_6(k):
    R = lambda v:And(Or([And(v[0] <= i+2,v[0] >= i,v[1] >= i,v[1] <= i+2,v[2] >= i,v[2] <= i+2,v[3] >= i,v[3] <= i+2,v[4] >= i,v[4] <= i+2,v[5] >= i,v[5] <= i+2) for
                        i in range(1,k)]),
                    And(v[0] + v[1] + v[2] + v[3] + v[4] + v[5]<= k))
    x, y, z, a,b,c= Consts('x y z a b c', IntSort())
    res = mondec(R, [x, y, z,a,b,c])
    #assert(isUnsat(res != R([x, y, z,a,b,c])))             #check correctness 
    print("mondec1(", R([x, y, z,a,b,c]), ") =", res)
   
def test_mondec14(k):
    R = lambda v:Or(Or([And(v[0] <= i+2,v[0] >= i,v[1] >= i,v[1] <= i+2,v[2] >= i,v[2] <= i+2) for
                        i in range(1,k)]),
                    And(v[0] + v[1] + v[2] == k,v[0] >= 0, v[1] >= 0, v[2] >= 0))
    x, y, z = Consts('x y z', IntSort())
    res = mondec(R, [x, y, z])
    #assert(isUnsat(res != R([x, y, z])))             #check correctness 
    print("mondec1(", R([x, y, z]), ") =", res)

def test_mondec15_3(k):
    R = lambda v:Or([And(v[0] <= i+2,v[0] >= i,v[1] >= i,v[1] <= i+2,v[2] >= i,v[2] <= i+2) for
                        i in range(1,k)])
    x, y, z = Consts('x y z', IntSort())
    res = mondec(R, [x, y, z])
    #assert(isUnsat(res != R([x, y, z])))             #check correctness 
    print("mondec1(", R([x, y, z]), ") =", res)
    
def test_mondec15_4(k):
    R = lambda v:Or([And(v[0] <= i+2,v[0] >= i,v[1] >= i,v[1] <= i+2,v[2] >= i,v[2] <= i+2,v[3] >= i,v[3] <= i+2) for
                        i in range(1,k)])
    x, y, z, a = Consts('x y z a', IntSort())
    res = mondec(R, [x, y, z,a])
    #assert(isUnsat(res != R([x, y, z,a])))             #check correctness 
    print("mondec1(", R([x, y, z,a]), ") =", res)


def test_mondec15_5(k):
    R = lambda v:Or([And(v[0] <= i+2,v[0] >= i,v[1] >= i,v[1] <= i+2,v[2] >= i,v[2] <= i+2,v[3] >= i,v[3] <= i+2,v[4] >= i,v[4] <= i+2) for
                        i in range(1,k)])
    x, y, z, a,b= Consts('x y z a b', IntSort())
    res = mondec(R, [x, y, z,a,b])
    #assert(isUnsat(res != R([x, y, z,a,b])))             #check correctness 
    print("mondec1(", R([x, y, z,a,b]), ") =", res)
    
def test_mondec15_10(k):
    R = lambda v:Or([And(v[0] <= i+2,v[0] >= i,v[1] >= i,v[1] <= i+2,v[2] >= i,v[2] <= i+2,v[3] >= i,v[3] <= i+2,v[4] >= i,v[4] <= i+2,v[5] >= i,v[5] <= i+2,v[6] >= i,v[6] <= i+2,v[7] >= i,v[7] <= i+2,v[8] >= i,v[8] <= i+2,v[9] >= i,v[9] <= i+2) for
                        i in range(1,k)])
    x, y, z, a,b,c,d,e,f,g= Consts('x y z a b c d e f g', IntSort())
    res = mondec(R, [x, y, z, a,b,c,d,e,f,g])
    #assert(isUnsat(res != R([x, y, z, a,b,c,d,e,f,g])))             #check correctness 
    print("mondec1(", R([x, y, z, a,b,c,d,e,f,g]), ") =", res)
    	    
def cav2009_10vars():
	x0, x1, x2, x3, x4, x5, x6, x7, x8, x9  = Ints('x0 x1 x2 x3 x4 x5 x6 x7 x8 x9')
	var = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9]
	R = lambda v: And(0*v[7]-v[7]+0*v[9]+1*v[9]-1*v[0]+1*v[4]+1*v[5]+0*v[9] <= -1,1*v[9]+0*v[3]-1*v[9]-1*v[0]+0*v[2]-1*v[0]+0*v[7]+0*v[8]-1*v[5]+1*v[9] <= 1,0*v[2]+ 0*v[2]-1*v[5]+0*v[6]+0*v[8]+0*v[9]+0*v[8]+0*v[3]+1*v[5]-1*v[9] <= 0,0*v[7]+1*v[0]+0*v[6]+0*v[6]+0*v[1]+0*v[7]+0*v[6]-1*v[4]+0*v[9]+1*v[8] <= 0, 1*v[3]+1*v[8]+0*v[1]+0*v[3]-1*v[3]+0*v[0]+0*v[2]+0*v[8]-1*v[2]+0*v[0] <= 0, -5 <= v[0], v[0] <= 5, -5 <= v[1], v[1] <= 5, -5 <= v[2], v[2] <= 5, -5 <= v[3], v[3] <= 5, -5 <= v[4], v[4] <= 5, -5 <= v[5], v[5] <= 5, -5 <= v[6], v[6] <= 5, -5 <= v[7], v[7] <= 5, -5 <= v[8], v[8] <= 5, -5 <= v[9], v[9] <= 5)
	res = mondec(R,var)
	#assert(isUnsat(res != R([x, y, z,a,b])))             #check correctness 	
	print("mondec1(", R([x, y, z,a,b]), ") =", res)

def cindy():
	b1,b2,b3,b4,b5,r  = Ints('b1 b2 b3 b4 b5 r')
	var = [r,b1,b2,b3,b4,b5]
	R = lambda b: Or(And(b[1] <= 20, b[2] <= 20, b[3] <= 10, b[4] <= 10, b[5] <= 0, b[0] == 1), And(b[1] <= 20, b[2] <= 20, b[3] <= 0, b[4] <= 10, b[5] <= 10, b[0] ==1), And(b[1] <= 10, b[2] <= 20, b[3] <= 20, b[4] <= 0, b[5]<= 10, b[0] == 2),And(b[1] <= 0, b[2] <= 20, b[3] <= 20, b[4] <= 10, b[5] <= 10, b[0]== 2), And(b[1] <= 10, b[2] <= 0, b[3] <= 20, b[4] <= 20, b[5] <= 10, b[0] == 3), And(b[1] <= 10, b[2] <= 10, b[3] <= 20, b[4] <= 20, b[5] <= 10, b[0] == 3), And(b[1] <= 0, b[2] <= 10, b[3] <= 10, b[4] <= 20, b[5] <= 20, b[0] == 4), And(b[1] <= 10, b[2]<= 10, b[3]<= 0, b[4] <= 20, b[5] <= 20, b[0] == 4), And(b[1] <= 20, b[2] <= 10, b[3] <= 10, b[4] <= 0, b[5] <= 20, b[0] == 5), And(b[1] <= 20, b[2] <= 0, b[3] <= 10, b[4] <= 10, b[5] <= 20, b[0] == 5), And(b[1] >= 0, b[2] >= 0, b[3] >= 0, b[4] >= 0, b[5] >=0))
	res = mondec(R,var)
	#assert(isUnsat(res != R([r,b1,b2,b3,b4,b5])))             #check correctness 	
	print("cindy(", R([r,b1,b2,b3,b4,b5]), ") =", res)
	
def cindy300c():
	b1,b2,b3,b4,b5,r  = Ints('b1 b2 b3 b4 b5 r')
	var = [r,b1,b2,b3,b4,b5]
	R = lambda b: Or(And(b[1] <= 200, b[2] <= 200, b[3] <= 100, b[4] <= 100, b[5] <= 0, b[0] == 1), And(b[1] <= 200, b[2] <= 200, b[3] <= 0, b[4] <= 100, b[5] <= 100, b[0] ==1), And(b[1] <= 100, b[2] <= 200, b[3] <= 200, b[4] <= 0, b[5]<= 100, b[0] == 2),And(b[1] <= 0, b[2] <= 200, b[3] <= 200, b[4] <= 100, b[5] <= 100, b[0]== 2), And(b[1] <= 100, b[2] <= 0, b[3] <= 200, b[4] <= 200, b[5] <= 100, b[0] == 3), And(b[1] <= 100, b[2] <= 100, b[3] <= 200, b[4] <= 200, b[5] <= 100, b[0] == 3), And(b[1] <= 0, b[2] <= 100, b[3] <= 100, b[4] <= 200, b[5] <= 200, b[0] == 4), And(b[1] <= 100, b[2]<= 100, b[3]<= 0, b[4] <= 200, b[5] <= 200, b[0] == 4), And(b[1] <= 200, b[2] <= 100, b[3] <= 100, b[4] <= 0, b[5] <= 200, b[0] == 5), And(b[1] <= 200, b[2] <= 0, b[3] <= 100, b[4] <= 100, b[5] <= 200, b[0] == 5), And(b[1] >= 0, b[2] >= 0, b[3] >= 0, b[4] >= 0, b[5] >=0))
	res = mondec(R,var)
	#assert(isUnsat(res != R([r,b1,b2,b3,b4,b5])))             #check correctness 	
	print("cindy(", R([r,b1,b2,b3,b4,b5]), ") =", res)


def cindy6b():
	b1,b2,b3,b4,b5,b6,r  = Ints('b1 b2 b3 b4 b5 b6 r')
	var = [r,b1,b2,b3,b4,b5,b6]
	R = lambda b: Or(And(b[1] <= 20, b[2] <= 20, b[3] <= 10, b[4] <= 10, b[5] <= 0, b[6] <= 0, b[0] == 1),And(b[1] <= 10, b[2] <= 10, b[3] <= 0, b[4] <= 0, b[5] <= 20, b[6] <= 20, b[0] == 5),And(b[1] <= 0, b[2] <= 0, b[3] <= 20, b[4] <= 20, b[5] <= 10, b[6] <= 10, b[0] == 3), And(b[1] <= 20, b[2] <= 20, b[3] <= 0, b[4] <= 0, b[5] <= 10, b[6] <= 10, b[0] ==1), And(b[1] <= 10, b[2] <= 20, b[3] <= 20, b[4] <= 0, b[5]<= 10, b[6] <= 10, b[0] == 2),And(b[1] <= 0, b[2] <= 20, b[3] <= 20, b[4] <= 10, b[5] <= 10, b[6] <= 10, b[0]== 2), And(b[1] <= 10, b[2] <= 0, b[3] <= 20, b[4] <= 20, b[5] <= 10, b[6] <= 10, b[0] == 3), And(b[1] <= 10, b[2] <= 10, b[3] <= 20, b[4] <= 20, b[5] <= 10, b[6] <= 10, b[0] == 3), And(b[1] <= 0, b[2] <= 10, b[3] <= 10, b[4] <= 20, b[5] <= 20, b[6] <= 0, b[0] == 4), And(b[1] <= 10, b[2]<= 10, b[3]<= 0, b[4] <= 20, b[5] <= 20, b[6] <= 0, b[0] == 4), And(b[1] <= 0, b[2] <= 10, b[3] <= 10, b[4] <= 0, b[5] <= 20, b[6] <= 20, b[0] == 5), And(b[1] <= 0, b[2] <= 0, b[3] <= 10, b[4] <= 10, b[5] <= 20, b[6] <= 20, b[0] == 5), And(b[1] >= 0, b[2] >= 0, b[3] >= 0, b[4] >= 0, b[5] >=0, b[6] >= 0))
	res = mondec(R,var)
	#assert(isUnsat(res != R([r,b1,b2,b3,b4,b5,b6])))             #check correctness 	
	print("cindy(", R([r,b1,b2,b3,b4,b5,b6]), ") =", res)

def cindy6b300c():
	b1,b2,b3,b4,b5,b6,r  = Ints('b1 b2 b3 b4 b5 b6 r')
	var = [r,b1,b2,b3,b4,b5,b6]
	R = lambda b: Or(And(b[1] <= 200, b[2] <= 200, b[3] <= 100, b[4] <= 100, b[5] <= 0, b[6] <= 0, b[0] == 1),And(b[1] <= 100, b[2] <= 100, b[3] <= 0, b[4] <= 0, b[5] <= 200, b[6] <= 200, b[0] == 5),And(b[1] <= 0, b[2] <= 0, b[3] <= 200, b[4] <= 200, b[5] <= 100, b[6] <= 100, b[0] == 3), And(b[1] <= 200, b[2] <= 200, b[3] <= 0, b[4] <= 0, b[5] <= 100, b[6] <= 100, b[0] ==1), And(b[1] <= 100, b[2] <= 200, b[3] <= 200, b[4] <= 0, b[5]<= 100, b[6] <= 100, b[0] == 2),And(b[1] <= 0, b[2] <= 200, b[3] <= 200, b[4] <= 100, b[5] <= 100, b[6] <= 100, b[0]== 2), And(b[1] <= 100, b[2] <= 0, b[3] <= 200, b[4] <= 200, b[5] <= 100, b[6] <= 100, b[0] == 3), And(b[1] <= 100, b[2] <= 100, b[3] <= 20, b[4] <= 200, b[5] <= 100, b[6] <= 100, b[0] == 3), And(b[1] <= 0, b[2] <= 100, b[3] <= 100, b[4] <= 200, b[5] <= 200, b[6] <= 0, b[0] == 4), And(b[1] <= 100, b[2]<= 100, b[3]<= 0, b[4] <= 200, b[5] <= 200, b[6] <= 0, b[0] == 4), And(b[1] <= 0, b[2] <= 100, b[3] <= 100, b[4] <= 0, b[5] <= 200, b[6] <= 200, b[0] == 5), And(b[1] <= 0, b[2] <= 0, b[3] <= 100, b[4] <= 100, b[5] <= 200, b[6] <= 200, b[0] == 5), And(b[1] >= 0, b[2] >= 0, b[3] >= 0, b[4] >= 0, b[5] >=0, b[6] >= 0))
	res = mondec(R,var)
	#assert(isUnsat(res != R([r,b1,b2,b3,b4,b5,b6])))             #check correctness 	
	print("cindy(", R([r,b1,b2,b3,b4,b5,b6]), ") =", res)

def cindy6b300cminw():
	b1,b2,b3,b4,b5,b6,r  = Ints('b1 b2 b3 b4 b5 b6 r')
	var = [r,b1,b2,b3,b4,b5,b6]
	R = lambda b: Or(And(b[1] <= 200, b[2] <= 200, b[3] <= 100, b[4] <= 100, b[5] <= 0, b[6] <= 0, b[0] == 1),And(b[1] <= 0, b[2] <= 0, b[3] <= 200, b[4] <= 200, b[5] <= 100, b[6] <= 100, b[0] == 3),And(b[1] <= 200, b[2] <= 200, b[3] <= 0, b[4] <= 0, b[5] <= 200, b[6] <= 200, b[0] == 5))
	res = mondec(R,var)
	#assert(isUnsat(res != R([r,b1,b2,b3,b4,b5,b6])))             #check correctness 	
	print("cindy(", R([r,b1,b2,b3,b4,b5,b6]), ") =", res)
	
def control_unit(k):
    var = []
    for i in range (0,k):
        placeholder = Int(i)
        var.append(placeholder)
    R = lambda v:Or([And(Or(And(1 <= v[i], v[i] <= 5, v[k-1]  == 0), And(2 <= v[i], v[i] <= 4, v[k-1]  == 1))) for i in range(0,k)])
    res = mondec(R, var)
    #assert(isUnsat(res != R(var)))             #check correctness 
    print("mondec1(", R(var), ") =", res)		

def mondec_implies(k):
	x,y  = Ints('x y')
	var = [x,y]
	R = lambda b: Implies(And(0 <= b[0], b[0] <= k),And(0 <= b[1], b[0] +b[1] <=k))
	res = mondec(R,var)
	#assert(isUnsat(res != R([x,y])))             #check correctness 	

def mondec_implies2(k):
	x,y  = Ints('x y')
	var = [x,y]
	R = lambda b: Implies(0 <= b[0],And(0 <= b[1], b[0] +b[1] >=k))
	res = mondec(R,var)
	#assert(isUnsat(res != R([x,y])))             #check correctness 	
	#print("cindy(", R([x,y]), ") =", res)

def diagonal(k):
	x,y  = Ints('x y')
	var = [x,y]
	R = lambda b: And(b[0] == b[1], b[0] >= 0, b[0] <= k, b[1] >= 0, b[1] <= k)
	res = mondec(R,var)
	#assert(isUnsat(res != R([x,y])))             #check correctness 	


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
	# arg2 : parameter k for suites 1-4
	# arg3 : parameter d for suite 4
	
	
	if sys.argv[1] == "dia-r":
		print("\n Running test on diagonal restricted... \n", sys.argv[1], " Parameter k: ", sys.argv[2])
		start = time.time()
		test_mondec10(int(sys.argv[2]))
		end = time.time()
		print("Total time needed: ", end - start)
	elif sys.argv[1] == "dia-u":
		print("\n Running test on diagonal unrestricted... \n", sys.argv[1], " Parameter k: ", sys.argv[2])
		start = time.time()
		test_mondec2(int(sys.argv[2]))	
		end = time.time()
		print("Total time needed: ", end - start)
	elif sys.argv[1] == "big-c":
		print("\n Running test on big overlapping cube... \n", sys.argv[1], " Parameter k: ", sys.argv[2])
		start = time.time()
		test_mondec9(int(sys.argv[2]))
		end = time.time()
		print("Total time needed: ", end - start)
	elif sys.argv[1] == "k-cubes":
		print("\n Running test on k overlapping cube... \n", sys.argv[1], " Parameter k: ", sys.argv[2], "Dimension d: ", sys.argv[3])
		if int(sys.argv[3]) == 2:
			start = time.time()
			test_mondec10(int(sys.argv[2]))
			end = time.time()
			print("Total time needed: ", end - start)
		elif int(sys.argv[3]) == 3:
			start = time.time()
			test_mondec15_3(int(sys.argv[2]))
			end = time.time()
			print("Total time needed: ", end - start)
		elif int(sys.argv[3]) == 4:
			start = time.time()
			test_mondec15_4(int(sys.argv[2]))
			end = time.time()
			print("Total time needed: ", end - start)
		elif int(sys.argv[3]) == 5:
			start = time.time()
			test_mondec15_5(int(sys.argv[2]))
			end = time.time()
			print("Total time needed: ", end - start)
		elif int(sys.argv[3]) == 10:
			start = time.time()
			test_mondec15_10(int(sys.argv[2]))
			end = time.time()
			print("Total time needed: ", end - start)
		else:
			print("Benchmark not implemented")
	elif sys.argv[1] == "k-dia":
		start = time.time()
		diagonal(int(sys.argv[2]))	
		end = time.time()	
		print("Total time needed: ", end - start)
	elif sys.argv[1] == "mondec":
		start = time.time()
		mondec_implies2(int(sys.argv[2]))	
		end = time.time()		
		print("Total time needed: ", end - start)		
	else:
		print("Command ", sys.argv[1], "  not recognized")

import ctypes, itertools

cadical = ctypes.CDLL("libcadical.dylib")

ipasir_signature = cadical.ipasir_signature
ipasir_signature.argtypes = []
ipasir_signature.restype = ctypes.c_char_p

ipasir_init = cadical.ipasir_init
ipasir_init.argtypes = []
ipasir_init.restype = ctypes.c_void_p

ipasir_release = cadical.ipasir_release
ipasir_release.argtypes = [ctypes.c_void_p]
ipasir_release.restype = None

ipasir_add = cadical.ipasir_add
ipasir_add.argtypes = [ctypes.c_void_p, ctypes.c_int32]
ipasir_add.restype = None

ipasir_assume = cadical.ipasir_assume
ipasir_assume.argtypes = [ctypes.c_void_p, ctypes.c_int32]
ipasir_assume.restype = None

ipasir_solve = cadical.ipasir_solve
ipasir_solve.argtypes = [ctypes.c_void_p]
ipasir_solve.restype = ctypes.c_int

ipasir_val = cadical.ipasir_val
ipasir_val.argtypes = [ctypes.c_void_p, ctypes.c_int32]
ipasir_val.restype = ctypes.c_int32

ipasir_failed = cadical.ipasir_failed
ipasir_failed.argtypes = [ctypes.c_void_p, ctypes.c_int32]
ipasir_failed.restype = ctypes.c_int

terminate = ctypes.CFUNCTYPE(ctypes.c_int, ctypes.c_void_p)

ipasir_set_terminate = cadical.ipasir_set_terminate
ipasir_set_terminate.argtypes = [ctypes.c_void_p, ctypes.c_void_p, terminate]
ipasir_set_terminate.restype = None

learn = ctypes.CFUNCTYPE(None, ctypes.c_void_p, ctypes.POINTER(ctypes.c_int32))

ipasir_set_learn = cadical.ipasir_set_learn
ipasir_set_learn.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int, learn]
ipasir_set_learn.restype = None

@learn
def print_learn(data, clause):
    print(end="a")
    for i in itertools.count():
        x = clause[i]
        print("", x, end="")
        if x == 0:
            break
    print()

print(ipasir_signature().decode())

solver = ipasir_init()

for i in 1, 2, 0, 1, -2, 0, -1, 2, 0, -1, -2, 0:
    ipasir_add(solver, i)

ipasir_set_learn(solver, None, 0x7fffffff, print_learn)

print(ipasir_solve(solver))

ipasir_release(solver)

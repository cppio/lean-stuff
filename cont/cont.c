#include <lean/lean.h>
#include <setjmp.h>

lean_object *Cont_throw(lean_object *k, lean_object *x) {
    longjmp(*(jmp_buf *)lean_sarray_cptr(k), (int)x);
    return 0;
}

lean_object *Cont_callcc(lean_object *f) {
    lean_object *k = lean_alloc_sarray(1, sizeof(jmp_buf), sizeof(jmp_buf));
    lean_object *x = (lean_object *)setjmp(*(jmp_buf *)lean_sarray_cptr(k));
    if (x) {
        lean_dec(k);
        return x;
    }
    return lean_apply_1(f, k);
}

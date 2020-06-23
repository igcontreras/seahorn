// RUN: sea smt -O0 --dsa=sea-cs --horn-shadow-mem-optimize=false --horn-inter-proc-fmaps %s
// CHECK: ^unknown$
// XFAIL: *

#include <stdlib.h>

extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error(), 0))

// (int, int, int, fmap(defk(x)), fmap(defk(x)), fmap(defk(y)), fmap(defk(y)))
void modify_int(int *x, int *y, int v) {
  *x = v;
  *y = v;
}

int main() {

  int *p = (int *)malloc(2*sizeof(int));
  int *q = (int *)malloc(2 * sizeof(int));

  // p -> *p // defk(p)
  // q -> *q // defk(q)

  // x = p,  // x -> *p // defk(x)
  modify_int(p, q, 42);

  sassert(*p == 42 && *q == 42);

  return 0;
}

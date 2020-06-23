// RUN: sea smt -O0 --dsa=sea-cs --horn-shadow-mem-optimize=false --horn-inter-proc-fmaps %s
// CHECK: ^unknown$
// XFAIL: *

#include <stdlib.h>

extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error(), 0))

int * p;

void modify_int(int *p, int *q, int v) {
  *p = v;
  *q = v;
}

int main() {
  p = (int *)malloc(2 * sizeof(int));
  int *q = (int *)malloc(2 * sizeof(int));

  modify_int(p, q, 42);

  sassert(*p == 42 && *q == 42);

  return 0;
}

// RUN: sea smt -O0 --dsa=sea-cs --horn-shadow-mem-optimize=false --horn-inter-proc-fmaps %s
// CHECK: ^unknown$
// XFAIL: *

#include <stdlib.h>

extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error(), 0))

void modify_int(int *p, int v) { *p = v; }

int main() {
  int *p = (int *)malloc(2*sizeof(int));

  p[1] = 43;

  modify_int(p, 42);

  sassert(*p == 42);

  return 0;
}

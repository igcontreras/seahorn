// RUN: sea smt -O0 --dsa=sea-cs --horn-shadow-mem-optimize=false --horn-inter-proc-fmaps %s

// CHECK: ^unknown$ XFAIL: *

#include <stdlib.h>

extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error(), 0))

typedef struct LElem {
  struct LElem *n1;
  struct LElem *n2;
} LElem;

void add_to_end(LElem *e) {
  LElem *n1 = (LElem * )malloc(sizeof(LElem));
  LElem *n2 = (LElem * )malloc(sizeof(LElem));

  e->n1 = n1;
  e->n1 = n2;

  e->n1->n1 = e->n1->n2;

  e->n1->n1 = 0;

}

int main() {
  LElem e1;

  add_to_end(&e1);

  sassert(e1.n1->n1 == 0);
  return 0;
}

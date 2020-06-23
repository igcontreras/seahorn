// RUN: sea smt -O0 --dsa=sea-cs --horn-shadow-mem-optimize=false
// --horn-inter-proc-fmaps %s CHECK: ^unknown$ XFAIL: *

#include <stdlib.h>

extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error(), 0))

typedef struct LElem {
  int data;
  struct LElem *next;
} LElem;

void add_to_end(LElem *e) {
  LElem *newe = (LElem * )malloc(sizeof(LElem));

  e->next = newe;
  newe->next = 0;

}

int main() {
  LElem e1;

  add_to_end(&e1);

  sassert(e1.next->next == 0);

  return 0;
}

// RUN: sea smt -O0 --dsa=sea-cs --horn-shadow-mem-optimize=false --horn-inter-proc-fmaps %s
// CHECK: ^unknown$
// XFAIL: *

extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error(), 0))

typedef struct S {
  struct S *x;
  struct S *y;
} S;

extern S * nd_S(void);

void foo(S * s) {
  s->x = 0;
  s->y = 0;
}

int main() {
  S * a = nd_S(), * b = nd_S();

  foo(a);
  foo(b);

  sassert(a->x == 0);

  return 0;
}

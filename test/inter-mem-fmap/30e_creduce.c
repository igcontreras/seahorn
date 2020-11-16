// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^unsat$

struct a {
  _Bool b;
  char c;
} d(long);
short e(short);
void f(void);

void g(int);
_Bool h(struct a *i, char *p2) {
  int j, k;
  d(i->b);
  g(k);
  *p2 = e(j);
  f();
}
int l(struct a *i) {
  h(i, 0);
  // h(i, &i->c);
}
void m() { l(m); }
void __VERIFIER_error() {}

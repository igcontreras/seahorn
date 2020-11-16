// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^unsat$

int b;
void __VERIFIER_error();
static void a() { __VERIFIER_error(); }
int main(void);
void c() {
  if (b < 5)
    b = b + 1;
}
void d() {
  while (1)
    if (b)
      ;
    else
      break;
  a();
}

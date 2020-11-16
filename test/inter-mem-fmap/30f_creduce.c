// RUN: sea pf -O0 --dsa=sea-cs --horn-vcgen-use-ite --horn-array-global-constraints --horn-use-write=false  --horn-global-constraints --horn-shadow-mem-optimize=false --horn-inter-proc-mem-fmaps --horn-fmap-max-keys=5 %s
// CHECK: ^unsat$

struct a {};
union b {
  struct a c;
  int d
};
struct {
  union b e
} f = {{}};
struct aa {
  void *g
};
struct ab {
  int h
};
struct i {
  char ac
};
struct j {
  struct i *ae
} * l;
k, n;
m(int);
o(struct aa *p) {
  char q;
  int a, r;
  s(r);
  l = m(a);
  p->g = l;
  if (q)
    t(f);
  u(n, s, "");
  l->ae->ac = 0;
}
v(struct aa *p) {
  struct j *w = p->g = &w;
  u();
  struct ab *b;
  b->h = o;
  __VERIFIER_error();
}
int main() {
 ak:
  v(&k);
  o(k);
  goto ak;
}


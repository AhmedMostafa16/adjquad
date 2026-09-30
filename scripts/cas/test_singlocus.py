"""Oracle test for check_singlocus (TDD: written before the module)."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_singlocus import affine_dim, bridge_ok, jacobian_ideal_gens

def _check(name, cond):
    print(("PASS" if cond else "FAIL") + " " + name)
    return bool(cond)

def main():
    ok = True
    G = jacobian_ideal_gens()
    ok &= _check("7 generators (S + 6 partials)", len(G) == 7)
    ok &= _check("generator S matches a-variable S (bridge)", bridge_ok())
    ok &= _check("singular locus dim < 5", affine_dim() <= 4)
    print("test_singlocus OK" if ok else "test_singlocus FAILED")
    return 0 if ok else 1

if __name__ == "__main__":
    raise SystemExit(main())

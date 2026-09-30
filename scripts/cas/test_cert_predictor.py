"""Oracle test for cert_predictor (TDD: written before the module)."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from cert_predictor import predict


def _check(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    return bool(cond)


def main():
    ok = True
    p14 = predict(14)
    p24 = predict(24)
    ok &= _check("genMonos 55 @14, 213 @24",
                 p14["genMonos"] == 55 and p24["genMonos"] == 213)
    ok &= _check("D0 nonzero; D0(24)==D0(14)",
                 p14["D0"] != 0 and p24["D0"] == p14["D0"])
    ok &= _check("density in (0,1]",
                 all(0 < p["density"] <= 1 for p in (p14, p24)))
    print("test_cert_predictor OK" if ok else "test_cert_predictor FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())

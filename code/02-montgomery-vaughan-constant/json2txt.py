import sys, json
D = json.load(open(sys.argv[1])); g = D["gaps"]; N = len(g) + 1
with open(sys.argv[2], "w") as f:
    f.write("%d\n" % N); f.write(" ".join(str(int(x)) for x in g) + "\n")
    for a, b in zip(D["w_re"], D["w_im"]): f.write("%d %d\n" % (int(a), int(b)))

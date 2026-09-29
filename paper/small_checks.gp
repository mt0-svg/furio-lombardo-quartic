\\ The checks printed in the introduction of the paper. Run: gp -q small_checks.gp < /dev/null
F(x, y, z) = x^4 + 3*x^3*y - 3*x^2*y*z - 3*x^2*z^2 + 6*x*y^3 - 6*x*y^2*z + 3*x*y*z^2 - 2*x*z^3 + 4*y^4 + 2*y^3*z - 5*y*z^3;
print([F(0, 0, 1), F(1, 1, 1), F(2, 0, 1), F(-1, 0, 1)]);
\\ primitive integer solutions with |x|, |y|, |z| <= 100, the last nonzero coordinate positive
H = 100; S = List();
for (x = -H, H, for (y = -H, H, for (z = -H, H, my(l = if (z, z, if (y, y, x))); if (l > 0 && gcd([x, y, z]) == 1 && F(x, y, z) == 0, listput(S, [x, y, z])))));
print(Vec(S));
\\ (a, b, c) = (13, -1, -1) solves a^2 + 196 b^3 = 27 c^7
print(13^2 + 196*(-1)^3 - 27*(-1)^7);
quit

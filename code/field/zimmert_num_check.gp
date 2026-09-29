\\ Numerical check of FurioLombardo/M2/ZimmertNum.lean: closed form of zimmertS2 3 9 (1/2) (1/12)
\\ and the rational constants used in the Lean proof of zimmertS2_half_ge.
default(realprecision, 60);
S2(r1,r2,g,a) = r1*(-psi((1+g)/2) - lngamma(1/2+g) + lngamma(1+g) + log(Pi)/2) + r2*(-2*psi(1+g) + 2*log(2) + log(1/2+g) + log(Pi)) - 2/(g-a) - log((1+1/a)*(1+1/g)^(-2)*(1+1/(2*g-a))^(-1));
v = S2(3,9,1/2,1/12);
c = 21*Euler - 3*Pi/2 + 60*log(2) + 12*log(Pi) - 204/5 + log(207/143);
L = log(sqrt(2^22*7^27)) - log(120000);
print("S2 = ", v, "\nclosed form - S2 = ", c - v, "\nLHS = ", L, "\nslack = ", v - L);
S(x,n) = sum(i=0,n-1, x^(i+1)/(i+1));
H16 = sum(j=1,16,1/j); print("H16 = ", H16);
x=1/8; u7 = -S(x,6) + x^7/(1-x);
x=2147/10000; lpi = -S(x,6) - x^7/(1-x);
x=64/207; lr = S(x,8) - x^9/(1-x);
c7 = -13353/100000; cpi = -24172/100000; cr = 3698/10000;
print("series bounds valid: ", [u7 <= c7, cpi <= lpi, cr <= lr, 7853/10000 <= 3141592/10^6/4]);
L2lo = 6931471803/10^10; L2hi = 6931471808/10^10; L3lo = 10986122885/10^10; L5lo = 16094379123/10^10; pihi = 3141593/10^6;
gl = H16 - 4*L2hi - 1/32; print("gamma lower bound error: ", Euler - gl);
m = 21*gl - 3*pihi/2 + 12*cpi + cr - 204/5 + (77/2)*L2lo - 27/2*c7 + L3lo + 4*L5lo;
print("certified margin (rational bounds) = ", m*1.);

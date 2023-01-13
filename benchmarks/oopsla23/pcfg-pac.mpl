p := 0.1; # Probability of S->SS rather than S->a
answer := proc(len)
  option remember;
  local i;
  if len = 0 then 0
  elif len = 1 then 1-p
  else p * add(answer(i) * answer(len-i), i=1..len-1)
  end if;
end proc;

with(Statistics):

# Given parsed string length, target relative accuracy, and (curried) rejection sample count,
# compute probability of getting an accurate estimate of truth
pac := proc(len,acc)
  local ans;
  ans := answer(len);
  n -> CumulativeDistributionFunction(Binomial(n, ans), (1+acc)*n*ans, numeric) -
       CumulativeDistributionFunction(Binomial(n, ans), (1-acc)*n*ans, numeric)
end proc;
pac(10,0.05)(1e9);

bisection := proc(f, target)
  local x1, x2, x;
  x1 := 1;
  x2 := 1;
  while f(x2) < target do x2 := x2 * 2; end do;
  while x1+1 < x2 do
    x := floor((x1+x2)/2);
    if f(x) < target then x1 := x; else x2 := x; end if;
  end do;
  x2
end proc;
bisection(pac(10,0.05), 0.95);

# For each parsed string length from 1 to 20, how many rejection samples does it take for the estimated probability to be within 5% of the truth 95% of the time?
seq(bisection(pac(len,0.05), 0.95), len=1..20);